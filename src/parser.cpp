/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 * 
 * This file implements the parsing logic that converts syntax trees into
 * expression trees that can be evaluated.
 * primitive operations, and function applications.
 */

#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>

#define mp make_pair
using std::string;
using std::vector;
using std::pair;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/**
 * @brief Default parse method (should be overridden by subclasses)
 */
Expr Syntax::parse(Assoc &env) {
    throw RuntimeError("Unimplemented parse method");
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    return Expr(new RationalNum(numerator, denominator));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        // Empty list literal -> '()
        return Expr(new Quote(Syntax(new List())));
    }

    // If first element is not a symbol, treat as ((expr) args...) apply
    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id == nullptr) {
        // Parse operator and operands
        Expr rator = stxs[0]->parse(env);
        vector<Expr> params;
        for (size_t i = 1; i < stxs.size(); ++i) params.push_back(stxs[i]->parse(env));
        return Expr(new Apply(rator, params));
    }

    string op = id->s;

    // Handle primitives (built-in procedures)
    if (primitives.count(op) != 0) {
        vector<Expr> parameters;
        for (size_t i = 1; i < stxs.size(); ++i) parameters.push_back(stxs[i]->parse(env));

        ExprType op_type = primitives[op];
        switch (op_type) {
            case E_PLUS:
                if (parameters.size() == 2) return Expr(new Plus(parameters[0], parameters[1]));
                return Expr(new PlusVar(parameters));
            case E_MINUS:
                if (parameters.size() == 1) return Expr(new Minus(parameters[0], Expr(new Fixnum(0)))); // Will be handled in eval var-arg too
                if (parameters.size() == 2) return Expr(new Minus(parameters[0], parameters[1]));
                return Expr(new MinusVar(parameters));
            case E_MUL:
                if (parameters.size() == 2) return Expr(new Mult(parameters[0], parameters[1]));
                return Expr(new MultVar(parameters));
            case E_DIV:
                if (parameters.size() == 2) return Expr(new Div(parameters[0], parameters[1]));
                return Expr(new DivVar(parameters));
            case E_MODULO:
                if (parameters.size() != 2) throw RuntimeError("Wrong number of arguments for modulo");
                return Expr(new Modulo(parameters[0], parameters[1]));
            case E_EXPT:
                if (parameters.size() != 2) throw RuntimeError("Wrong number of arguments for expt");
                return Expr(new Expt(parameters[0], parameters[1]));
            case E_CONS:
                if (parameters.size() != 2) throw RuntimeError("Wrong number of arguments for cons");
                return Expr(new Cons(parameters[0], parameters[1]));
            case E_CAR:
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for car");
                return Expr(new Car(parameters[0]));
            case E_CDR:
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for cdr");
                return Expr(new Cdr(parameters[0]));
            case E_LIST:
                return Expr(new ListFunc(parameters));
            case E_SETCAR:
                if (parameters.size() != 2) throw RuntimeError("Wrong number of arguments for set-car!");
                return Expr(new SetCar(parameters[0], parameters[1]));
            case E_SETCDR:
                if (parameters.size() != 2) throw RuntimeError("Wrong number of arguments for set-cdr!");
                return Expr(new SetCdr(parameters[0], parameters[1]));
            case E_LT:
                if (parameters.size() == 2) return Expr(new Less(parameters[0], parameters[1]));
                return Expr(new LessVar(parameters));
            case E_LE:
                if (parameters.size() == 2) return Expr(new LessEq(parameters[0], parameters[1]));
                return Expr(new LessEqVar(parameters));
            case E_EQ:
                if (parameters.size() == 2) return Expr(new Equal(parameters[0], parameters[1]));
                return Expr(new EqualVar(parameters));
            case E_EQQ:
                if (parameters.size() != 2) throw RuntimeError("Wrong number of arguments for eq?");
                return Expr(new IsEq(parameters[0], parameters[1]));
            case E_GE:
                if (parameters.size() == 2) return Expr(new GreaterEq(parameters[0], parameters[1]));
                return Expr(new GreaterEqVar(parameters));
            case E_GT:
                if (parameters.size() == 2) return Expr(new Greater(parameters[0], parameters[1]));
                return Expr(new GreaterVar(parameters));
            case E_NOT:
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for not");
                return Expr(new Not(parameters[0]));
            case E_AND:
                return Expr(new AndVar(parameters));
            case E_OR:
                return Expr(new OrVar(parameters));
            case E_BOOLQ:
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for boolean?");
                return Expr(new IsBoolean(parameters[0]));
            case E_INTQ:
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for number?");
                return Expr(new IsFixnum(parameters[0]));
            case E_NULLQ:
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for null?");
                return Expr(new IsNull(parameters[0]));
            case E_PAIRQ:
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for pair?");
                return Expr(new IsPair(parameters[0]));
            case E_PROCQ:
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for procedure?");
                return Expr(new IsProcedure(parameters[0]));
            case E_SYMBOLQ:
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for symbol?");
                return Expr(new IsSymbol(parameters[0]));
            case E_LISTQ:
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for list?");
                return Expr(new IsList(parameters[0]));
            case E_STRINGQ:
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for string?");
                return Expr(new IsString(parameters[0]));
            case E_DISPLAY:
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for display");
                return Expr(new Display(parameters[0]));
            case E_VOID:
                if (!parameters.empty()) throw RuntimeError("Wrong number of arguments for void");
                return Expr(new MakeVoid());
            case E_EXIT:
                if (!parameters.empty()) throw RuntimeError("Wrong number of arguments for exit");
                return Expr(new Exit());
            default:
                break;
        }
    }

    // Handle reserved words (special forms)
    if (reserved_words.count(op) != 0) {
        switch (reserved_words[op]) {
            case E_QUOTE: {
                if (stxs.size() != 2) throw RuntimeError("quote expects a single argument");
                return Expr(new Quote(stxs[1]));
            }
            case E_BEGIN: {
                vector<Expr> seq;
                for (size_t i = 1; i < stxs.size(); ++i) seq.push_back(stxs[i]->parse(env));
                return Expr(new Begin(seq));
            }
            case E_IF: {
                if (stxs.size() != 4) throw RuntimeError("if expects three arguments");
                Expr c = stxs[1]->parse(env);
                Expr t = stxs[2]->parse(env);
                Expr e = stxs[3]->parse(env);
                return Expr(new If(c, t, e));
            }
            case E_COND: {
                // Each clause is a list: (pred expr...)
                vector<vector<Expr>> clauses;
                for (size_t i = 1; i < stxs.size(); ++i) {
                    List* clauseList = dynamic_cast<List*>(stxs[i].get());
                    if (!clauseList) throw RuntimeError("cond clause must be a list");
                    vector<Expr> one;
                    for (auto &sx : clauseList->stxs) one.push_back(sx->parse(env));
                    if (one.empty()) throw RuntimeError("empty cond clause");
                    clauses.push_back(one);
                }
                return Expr(new Cond(clauses));
            }
            case E_LAMBDA: {
                if (stxs.size() < 3) throw RuntimeError("lambda expects parameters and body");
                // parameters must be a list of symbols
                List* params = dynamic_cast<List*>(stxs[1].get());
                if (!params) throw RuntimeError("lambda parameters must be a list");
                vector<string> xs;
                for (auto &sx : params->stxs) {
                    auto sym = dynamic_cast<SymbolSyntax*>(sx.get());
                    if (!sym) throw RuntimeError("lambda parameter must be a symbol");
                    xs.push_back(sym->s);
                }
                // Body: if multiple expressions, wrap in begin
                Expr body_expr = (stxs.size() == 3) ? stxs[2]->parse(env) : Expr(new Begin([&]{
                    vector<Expr> seq; for (size_t i = 2; i < stxs.size(); ++i) seq.push_back(stxs[i]->parse(env)); return seq; }()));
                return Expr(new Lambda(xs, body_expr));
            }
            case E_DEFINE: {
                if (stxs.size() < 3) throw RuntimeError("define expects at least 2 arguments");
                // (define var expr) or (define (fname args...) body...)
                if (auto sym = dynamic_cast<SymbolSyntax*>(stxs[1].get())) {
                    Expr val = (stxs.size() == 3) ? stxs[2]->parse(env)
                                                 : Expr(new Begin([&]{ vector<Expr> seq; for (size_t i = 2; i < stxs.size(); ++i) seq.push_back(stxs[i]->parse(env)); return seq; }()));
                    return Expr(new Define(sym->s, val));
                } else if (auto lst = dynamic_cast<List*>(stxs[1].get())) {
                    if (lst->stxs.empty()) throw RuntimeError("invalid define");
                    auto fname = dynamic_cast<SymbolSyntax*>(lst->stxs[0].get());
                    if (!fname) throw RuntimeError("invalid function name in define");
                    vector<string> xs;
                    for (size_t i = 1; i < lst->stxs.size(); ++i) {
                        auto p = dynamic_cast<SymbolSyntax*>(lst->stxs[i].get());
                        if (!p) throw RuntimeError("lambda parameter must be a symbol");
                        xs.push_back(p->s);
                    }
                    // Body
                    Expr body_expr = (stxs.size() == 3) ? stxs[2]->parse(env)
                                                       : Expr(new Begin([&]{ vector<Expr> seq; for (size_t i = 2; i < stxs.size(); ++i) seq.push_back(stxs[i]->parse(env)); return seq; }()));
                    return Expr(new Define(fname->s, Expr(new Lambda(xs, body_expr))));
                } else {
                    throw RuntimeError("invalid define form");
                }
            }
            case E_LET:
            case E_LETREC:
            case E_SET:
                // Parse but leave evaluation to evaluator (extensions)
                // let ((p1 v1) (p2 v2) ...) body...
                if (stxs.size() < 3) throw RuntimeError("binding form expects bindings and body");
                {
                    List* bindsList = dynamic_cast<List*>(stxs[1].get());
                    if (!bindsList) throw RuntimeError("bindings must be a list");
                    vector<pair<string, Expr>> binds;
                    for (auto &b : bindsList->stxs) {
                        List* pairList = dynamic_cast<List*>(b.get());
                        if (!pairList || pairList->stxs.size() != 2)
                            throw RuntimeError("each binding must be a pair");
                        auto nameSym = dynamic_cast<SymbolSyntax*>(pairList->stxs[0].get());
                        if (!nameSym) throw RuntimeError("binding name must be a symbol");
                        binds.push_back({nameSym->s, pairList->stxs[1]->parse(env)});
                    }
                    // Body
                    Expr body = (stxs.size() == 3) ? stxs[2]->parse(env)
                                                  : Expr(new Begin([&]{ vector<Expr> seq; for (size_t i = 2; i < stxs.size(); ++i) seq.push_back(stxs[i]->parse(env)); return seq; }()));
                    if (reserved_words[op] == E_LET)
                        return Expr(new Let(binds, body));
                    else if (reserved_words[op] == E_LETREC)
                        return Expr(new Letrec(binds, body));
                    else {
                        // set!
                        if (binds.size() != 1) throw RuntimeError("invalid set! form");
                        return Expr(new Set(binds[0].first, binds[0].second));
                    }
                }
            default:
                throw RuntimeError("Unknown reserved word: " + op);
        }
    }

    // default: treat as application to a variable/operator
    vector<Expr> params;
    for (size_t i = 1; i < stxs.size(); ++i) params.push_back(stxs[i]->parse(env));
    return Expr(new Apply(Expr(new Var(op)), params));
}

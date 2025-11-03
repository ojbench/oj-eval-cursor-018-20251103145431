/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 * 
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "value.hpp"
#include "expr.hpp" 
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>
#include <functional>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

Value Fixnum::eval(Assoc &e) { // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) { // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) { // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) { // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) { // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) { // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) { // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) { // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) { // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) { // evaluation of multi-operator primitive
    std::vector<Value> args;
    args.reserve(rands.size());
    for (auto &ex : rands) args.push_back(ex->eval(e));
    return evalRator(args);
}

Value Var::eval(Assoc &e) { // evaluation of variable
    // TODO: TO identify the invalid variable
    // We request all valid variable just need to be a symbol,you should promise:
    //The first character of a variable name cannot be a digit or any character from the set: {.@}
    //If a string can be recognized as a number, it will be prioritized as a number. For example: 1, -1, +123, .123, +124., 1e-3
    //Variable names can overlap with primitives and reserve_words
    //Variable names can contain any non-whitespace characters except #, ', ", `, but the first character cannot be a digit
    //When a variable is not defined in the current scope, your interpreter should output RuntimeError
    
    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
             static std::map<ExprType, std::pair<Expr, std::vector<std::string>>> primitive_map = {
                    {E_VOID,     {new MakeVoid(), {}}},
                    {E_EXIT,     {new Exit(), {}}},
                    {E_BOOLQ,    {new IsBoolean(new Var("parm")), {"parm"}}},
                    {E_INTQ,     {new IsFixnum(new Var("parm")), {"parm"}}},
                    {E_NULLQ,    {new IsNull(new Var("parm")), {"parm"}}},
                    {E_PAIRQ,    {new IsPair(new Var("parm")), {"parm"}}},
                    {E_PROCQ,    {new IsProcedure(new Var("parm")), {"parm"}}},
                    {E_SYMBOLQ,  {new IsSymbol(new Var("parm")), {"parm"}}},
                    {E_STRINGQ,  {new IsString(new Var("parm")), {"parm"}}},
                    {E_DISPLAY,  {new Display(new Var("parm")), {"parm"}}},
                    {E_PLUS,     {new PlusVar({}),  {}}},
                    {E_MINUS,    {new MinusVar({}), {}}},
                    {E_MUL,      {new MultVar({}),  {}}},
                    {E_DIV,      {new DivVar({}),   {}}},
                    {E_MODULO,   {new Modulo(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EXPT,     {new Expt(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EQQ,      {new IsEq(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
            };

            auto it = primitive_map.find(primitives[x]);
            //TOD0:to PASS THE parameters correctly;
            //COMPLETE THE CODE WITH THE HINT IN IF SENTENCE WITH CORRECT RETURN VALUE
            if (it != primitive_map.end()) {
                const auto &param_names = it->second.second;
                const auto &body_expr = it->second.first;
                return ProcedureV(param_names, body_expr, empty());
            }
      }
    }
    if (matched_value.get() == nullptr) {
        throw RuntimeError("undefined variable is undefined in the current scope");
    }
    return matched_value;
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) { // +
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int a = dynamic_cast<Integer*>(rand1.get())->n;
        int b = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(a + b);
    }
    int n1, d1, n2, d2;
    if (rand1->v_type == V_INT) { n1 = dynamic_cast<Integer*>(rand1.get())->n; d1 = 1; }
    else if (rand1->v_type == V_RATIONAL) { n1 = dynamic_cast<Rational*>(rand1.get())->numerator; d1 = dynamic_cast<Rational*>(rand1.get())->denominator; }
    else throw RuntimeError("Wrong typename");
    if (rand2->v_type == V_INT) { n2 = dynamic_cast<Integer*>(rand2.get())->n; d2 = 1; }
    else if (rand2->v_type == V_RATIONAL) { n2 = dynamic_cast<Rational*>(rand2.get())->numerator; d2 = dynamic_cast<Rational*>(rand2.get())->denominator; }
    else throw RuntimeError("Wrong typename");
    return RationalV(n1 * d2 + n2 * d1, d1 * d2);
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) { // -
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int a = dynamic_cast<Integer*>(rand1.get())->n;
        int b = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(a - b);
    }
    int n1, d1, n2, d2;
    if (rand1->v_type == V_INT) { n1 = dynamic_cast<Integer*>(rand1.get())->n; d1 = 1; }
    else if (rand1->v_type == V_RATIONAL) { n1 = dynamic_cast<Rational*>(rand1.get())->numerator; d1 = dynamic_cast<Rational*>(rand1.get())->denominator; }
    else throw RuntimeError("Wrong typename");
    if (rand2->v_type == V_INT) { n2 = dynamic_cast<Integer*>(rand2.get())->n; d2 = 1; }
    else if (rand2->v_type == V_RATIONAL) { n2 = dynamic_cast<Rational*>(rand2.get())->numerator; d2 = dynamic_cast<Rational*>(rand2.get())->denominator; }
    else throw RuntimeError("Wrong typename");
    return RationalV(n1 * d2 - n2 * d1, d1 * d2);
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) { // *
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int a = dynamic_cast<Integer*>(rand1.get())->n;
        int b = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(a * b);
    }
    int n1, d1, n2, d2;
    if (rand1->v_type == V_INT) { n1 = dynamic_cast<Integer*>(rand1.get())->n; d1 = 1; }
    else if (rand1->v_type == V_RATIONAL) { n1 = dynamic_cast<Rational*>(rand1.get())->numerator; d1 = dynamic_cast<Rational*>(rand1.get())->denominator; }
    else throw RuntimeError("Wrong typename");
    if (rand2->v_type == V_INT) { n2 = dynamic_cast<Integer*>(rand2.get())->n; d2 = 1; }
    else if (rand2->v_type == V_RATIONAL) { n2 = dynamic_cast<Rational*>(rand2.get())->numerator; d2 = dynamic_cast<Rational*>(rand2.get())->denominator; }
    else throw RuntimeError("Wrong typename");
    return RationalV(n1 * n2, d1 * d2);
}

Value Div::evalRator(const Value &rand1, const Value &rand2) { // /
    int n1, d1, n2, d2;
    if (rand1->v_type == V_INT) { n1 = dynamic_cast<Integer*>(rand1.get())->n; d1 = 1; }
    else if (rand1->v_type == V_RATIONAL) { n1 = dynamic_cast<Rational*>(rand1.get())->numerator; d1 = dynamic_cast<Rational*>(rand1.get())->denominator; }
    else throw RuntimeError("Wrong typename");
    if (rand2->v_type == V_INT) { n2 = dynamic_cast<Integer*>(rand2.get())->n; d2 = 1; }
    else if (rand2->v_type == V_RATIONAL) { n2 = dynamic_cast<Rational*>(rand2.get())->numerator; d2 = dynamic_cast<Rational*>(rand2.get())->denominator; }
    else throw RuntimeError("Wrong typename");
    if (n2 == 0) throw RuntimeError("Division by zero");
    return RationalV(n1 * d2, d1 * n2);
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) { // + with multiple args
    // 0 args -> 0
    if (args.empty()) return IntegerV(0);
    // Accumulate manually
    int n = 0; int num = 0, den = 1; bool isRat = false;
    for (auto &v : args) {
        if (v->v_type == V_INT && !isRat) {
            n += dynamic_cast<Integer*>(v.get())->n;
        } else {
            int a, b;
            if (v->v_type == V_INT) { a = dynamic_cast<Integer*>(v.get())->n; b = 1; }
            else if (v->v_type == V_RATIONAL) { a = dynamic_cast<Rational*>(v.get())->numerator; b = dynamic_cast<Rational*>(v.get())->denominator; }
            else throw RuntimeError("Wrong typename");
            if (!isRat) { num = n; den = 1; isRat = true; }
            num = num * b + a * den;
            den = den * b;
        }
    }
    if (!isRat) return IntegerV(n);
    return RationalV(num, den);
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args
    if (args.empty()) throw RuntimeError("- expects at least 1 argument");
    if (args.size() == 1) {
        // unary negation
        if (args[0]->v_type == V_INT) {
            int a = dynamic_cast<Integer*>(args[0].get())->n;
            return IntegerV(-a);
        } else if (args[0]->v_type == V_RATIONAL) {
            int a = dynamic_cast<Rational*>(args[0].get())->numerator;
            int b = dynamic_cast<Rational*>(args[0].get())->denominator;
            return RationalV(-a, b);
        } else {
            throw RuntimeError("Wrong typename");
        }
    }
    // Implement fold-left manually
    int num, den; bool isRat;
    auto init = args[0];
    if (init->v_type == V_INT) { num = dynamic_cast<Integer*>(init.get())->n; den = 1; isRat = false; }
    else if (init->v_type == V_RATIONAL) { num = dynamic_cast<Rational*>(init.get())->numerator; den = dynamic_cast<Rational*>(init.get())->denominator; isRat = true; }
    else throw RuntimeError("Wrong typename");
    for (size_t i = 1; i < args.size(); ++i) {
        int a, b;
        if (args[i]->v_type == V_INT) { a = dynamic_cast<Integer*>(args[i].get())->n; b = 1; }
        else if (args[i]->v_type == V_RATIONAL) { a = dynamic_cast<Rational*>(args[i].get())->numerator; b = dynamic_cast<Rational*>(args[i].get())->denominator; }
        else throw RuntimeError("Wrong typename");
        if (!isRat && b != 1) { isRat = true; }
        num = num * b - a * den;
        den = den * b;
    }
    if (!isRat && den == 1) return IntegerV(num);
    return RationalV(num, den);
}

Value MultVar::evalRator(const std::vector<Value> &args) { // * with multiple args
    if (args.empty()) return IntegerV(1);
    long long num = 1, den = 1; bool isRat = false;
    for (auto &v : args) {
        int a, b;
        if (v->v_type == V_INT) { a = dynamic_cast<Integer*>(v.get())->n; b = 1; }
        else if (v->v_type == V_RATIONAL) { a = dynamic_cast<Rational*>(v.get())->numerator; b = dynamic_cast<Rational*>(v.get())->denominator; isRat = true; }
        else throw RuntimeError("Wrong typename");
        num *= a; den *= b;
    }
    if (!isRat && den == 1) return IntegerV((int)num);
    return RationalV((int)num, (int)den);
}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args
    if (args.empty()) throw RuntimeError("/ expects at least 1 argument");
    if (args.size() == 1) {
        // reciprocal
        int a, b;
        if (args[0]->v_type == V_INT) { a = dynamic_cast<Integer*>(args[0].get())->n; b = 1; }
        else if (args[0]->v_type == V_RATIONAL) { a = dynamic_cast<Rational*>(args[0].get())->numerator; b = dynamic_cast<Rational*>(args[0].get())->denominator; }
        else throw RuntimeError("Wrong typename");
        if (a == 0) throw RuntimeError("Division by zero");
        return RationalV(b, a);
    }
    int num, den; bool isRat;
    if (args[0]->v_type == V_INT) { num = dynamic_cast<Integer*>(args[0].get())->n; den = 1; isRat = false; }
    else if (args[0]->v_type == V_RATIONAL) { num = dynamic_cast<Rational*>(args[0].get())->numerator; den = dynamic_cast<Rational*>(args[0].get())->denominator; isRat = true; }
    else throw RuntimeError("Wrong typename");
    for (size_t i = 1; i < args.size(); ++i) {
        int a, b;
        if (args[i]->v_type == V_INT) { a = dynamic_cast<Integer*>(args[i].get())->n; b = 1; }
        else if (args[i]->v_type == V_RATIONAL) { a = dynamic_cast<Rational*>(args[i].get())->numerator; b = dynamic_cast<Rational*>(args[i].get())->denominator; isRat = true; }
        else throw RuntimeError("Wrong typename");
        if (a == 0) throw RuntimeError("Division by zero");
        num = num * b; den = den * a;
    }
    if (!isRat && den == 1) return IntegerV(num);
    return RationalV(num, den);
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) { // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;
        
        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }
        
        long long result = 1;
        long long b = base;
        int exp = exponent;
        
        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }
        
        return IntegerV((int)result);
    }
    throw(RuntimeError("Wrong typename"));
}

//A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int left = r1->numerator;
        int right = n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = n1 * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) { // <
    return BooleanV(compareNumericValues(rand1, rand2) < 0);
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) { // <=
    return BooleanV(compareNumericValues(rand1, rand2) <= 0);
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) { // =
    return BooleanV(compareNumericValues(rand1, rand2) == 0);
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) { // >=
    return BooleanV(compareNumericValues(rand1, rand2) >= 0);
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) { // >
    return BooleanV(compareNumericValues(rand1, rand2) > 0);
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 1; i < args.size(); ++i) if (!(compareNumericValues(args[i-1], args[i]) < 0)) return BooleanV(false);
    return BooleanV(true);
}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 1; i < args.size(); ++i) if (!(compareNumericValues(args[i-1], args[i]) <= 0)) return BooleanV(false);
    return BooleanV(true);
}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 1; i < args.size(); ++i) if (!(compareNumericValues(args[i-1], args[i]) == 0)) return BooleanV(false);
    return BooleanV(true);
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 1; i < args.size(); ++i) if (!(compareNumericValues(args[i-1], args[i]) >= 0)) return BooleanV(false);
    return BooleanV(true);
}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 1; i < args.size(); ++i) if (!(compareNumericValues(args[i-1], args[i]) > 0)) return BooleanV(false);
    return BooleanV(true);
}

Value Cons::evalRator(const Value &rand1, const Value &rand2) { // cons
    return PairV(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) { // list function
    Value res = NullV();
    for (int i = (int)args.size() - 1; i >= 0; --i) res = PairV(args[i], res);
    return res;
}

Value IsList::evalRator(const Value &rand) { // list?
    if (rand->v_type == V_NULL) return BooleanV(true);
    if (rand->v_type != V_PAIR) return BooleanV(false);
    // Follow cdr chain to ensure it ends with null
    Value cur = rand;
    while (cur->v_type == V_PAIR) {
        cur = dynamic_cast<Pair*>(cur.get())->cdr;
    }
    return BooleanV(cur->v_type == V_NULL);
}

Value Car::evalRator(const Value &rand) { // car
    if (rand->v_type != V_PAIR) throw RuntimeError("car expects a pair");
    return dynamic_cast<Pair*>(rand.get())->car;
}

Value Cdr::evalRator(const Value &rand) { // cdr
    if (rand->v_type != V_PAIR) throw RuntimeError("cdr expects a pair");
    return dynamic_cast<Pair*>(rand.get())->cdr;
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!
    if (rand1->v_type != V_PAIR) throw RuntimeError("set-car! expects a pair");
    dynamic_cast<Pair*>(rand1.get())->car = rand2;
    return VoidV();
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!
   if (rand1->v_type != V_PAIR) throw RuntimeError("set-cdr! expects a pair");
   dynamic_cast<Pair*>(rand1.get())->cdr = rand2;
   return VoidV();
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) { // eq?
    // Check if type is Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    // Check if type is Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    // Check if type is Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    // Check if type is Null or Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) { // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) { // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) { // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) { // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) { // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) { // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) { // string?
    return BooleanV(rand->v_type == V_STRING);
}

Value Begin::eval(Assoc &e) {
    if (es.empty()) return VoidV();
    Value last = VoidV();
    for (size_t i = 0; i < es.size(); ++i) last = es[i]->eval(e);
    return last;
}

Value Quote::eval(Assoc& e) {
    // Convert Syntax tree to a quoted Value
    std::function<Value(const Syntax&)> quoteToValue = [&](const Syntax &s) -> Value {
        if (auto num = dynamic_cast<Number*>(s.get())) {
            return IntegerV(num->n);
        }
        if (auto rat = dynamic_cast<RationalSyntax*>(s.get())) {
            return RationalV(rat->numerator, rat->denominator);
        }
        if (dynamic_cast<TrueSyntax*>(s.get())) return BooleanV(true);
        if (dynamic_cast<FalseSyntax*>(s.get())) return BooleanV(false);
        if (auto str = dynamic_cast<StringSyntax*>(s.get())) return StringV(str->s);
        if (auto sym = dynamic_cast<SymbolSyntax*>(s.get())) return SymbolV(sym->s);
        if (auto lst = dynamic_cast<List*>(s.get())) {
            // Handle dotted list if exists
            int dotIndex = -1;
            for (size_t i = 0; i < lst->stxs.size(); ++i) {
                if (auto sym = dynamic_cast<SymbolSyntax*>(lst->stxs[i].get())) {
                    if (sym->s == ".") {
                        dotIndex = (int)i;
                        break;
                    }
                }
            }
            if (dotIndex == -1) {
                // proper list
                Value res = NullV();
                for (int i = (int)lst->stxs.size() - 1; i >= 0; --i)
                    res = PairV(quoteToValue(lst->stxs[i]), res);
                return res;
            } else {
                // dotted list: (a b . c)
                if (!(dotIndex + 1 < (int)lst->stxs.size())) throw RuntimeError("invalid dotted list");
                Value tail = quoteToValue(lst->stxs[dotIndex + 1]);
                for (int i = dotIndex - 1; i >= 0; --i) tail = PairV(quoteToValue(lst->stxs[i]), tail);
                return tail;
            }
        }
        throw RuntimeError("Unsupported quote syntax");
    };
    return quoteToValue(s);
}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation
    if (rands.empty()) return BooleanV(true);
    Value last = BooleanV(true);
    for (auto &ex : rands) {
        last = ex->eval(e);
        if (last->v_type == V_BOOL && !dynamic_cast<Boolean*>(last.get())->b) return BooleanV(false);
    }
    return last;
}

Value OrVar::eval(Assoc &e) { // or with short-circuit evaluation
    if (rands.empty()) return BooleanV(false);
    for (auto &ex : rands) {
        Value v = ex->eval(e);
        if (!(v->v_type == V_BOOL && dynamic_cast<Boolean*>(v.get())->b == false)) return v;
    }
    return BooleanV(false);
}

Value Not::evalRator(const Value &rand) { // not
    bool is_false = (rand->v_type == V_BOOL && dynamic_cast<Boolean*>(rand.get())->b == false);
    return BooleanV(is_false);
}

Value If::eval(Assoc &e) {
    Value c = cond->eval(e);
    bool truthy = !(c->v_type == V_BOOL && dynamic_cast<Boolean*>(c.get())->b == false);
    if (truthy) return conseq->eval(e);
    return alter->eval(e);
}

Value Cond::eval(Assoc &env) {
    for (auto &cl : clauses) {
        // Single element clause: return predicate value
        if (cl.size() == 1) {
            Value pv = cl[0]->eval(env);
            bool truthy = !(pv->v_type == V_BOOL && dynamic_cast<Boolean*>(pv.get())->b == false);
            if (truthy) return pv;
            else continue;
        }
        // else clause detection
        if (auto v = dynamic_cast<Var*>(cl[0].get())) {
            if (v->x == "else") {
                // evaluate sequence and return last
                Value last = VoidV();
                for (size_t i = 1; i < cl.size(); ++i) last = cl[i]->eval(env);
                return last;
            }
        }
        Value pv = cl[0]->eval(env);
        bool truthy = !(pv->v_type == V_BOOL && dynamic_cast<Boolean*>(pv.get())->b == false);
        if (truthy) {
            Value last = VoidV();
            for (size_t i = 1; i < cl.size(); ++i) last = cl[i]->eval(env);
            return last;
        }
    }
    return VoidV();
}

Value Lambda::eval(Assoc &env) { 
    return ProcedureV(x, e, env);
}

Value Apply::eval(Assoc &e) {
    Value rator_val = rator->eval(e);
    if (rator_val->v_type != V_PROC) {throw RuntimeError("Attempt to apply a non-procedure");}

    // Closure pointer
    Procedure* clos_ptr = dynamic_cast<Procedure*>(rator_val.get());
    
    //TODO: TO COMPLETE THE ARGUMENT PARSER LOGIC
    std::vector<Value> args;
    args.reserve(rand.size());
    for (auto &ex : rand) args.push_back(ex->eval(e));
    if (auto varNode = dynamic_cast<Variadic*>(clos_ptr->e.get())) {
        return varNode->evalRator(args);
    }
    if (args.size() != clos_ptr->parameters.size()) throw RuntimeError("Wrong number of arguments");
    
    //TODO: TO COMPLETE THE PARAMETERS' ENVIRONMENT LOGIC
    Assoc param_env = clos_ptr->env;
    for (size_t i = 0; i < clos_ptr->parameters.size(); ++i) {
        param_env = extend(clos_ptr->parameters[i], args[i], param_env);
    }

    return clos_ptr->e->eval(param_env);
}

Value Define::eval(Assoc &env) {
    // Placeholder binding first (for recursion), then evaluate and update
    env = extend(var, VoidV(), env);
    Value val = e->eval(env);
    modify(var, val, env);
    return SymbolV(var);
}

Value Let::eval(Assoc &env) {
    // let ((p1 v1) ...) body
    Assoc new_env = env;
    for (auto &b : bind) {
        Value v = b.second->eval(env);
        new_env = extend(b.first, v, new_env);
    }
    return body->eval(new_env);
}

Value Letrec::eval(Assoc &env) {
    // Create env1 with placeholders
    Assoc env1 = env;
    for (auto &b : bind) env1 = extend(b.first, Value(nullptr), env1);
    // Evaluate expressions in env1
    std::vector<Value> vals; vals.reserve(bind.size());
    for (auto &b : bind) vals.push_back(b.second->eval(env1));
    // Create env2 with actual bindings
    Assoc env2 = env;
    for (size_t i = 0; i < bind.size(); ++i) env2 = extend(bind[i].first, vals[i], env2);
    return body->eval(env2);
}

Value Set::eval(Assoc &env) {
    // set! var expr
    Value cur = find(var, env);
    if (cur.get() == nullptr) throw RuntimeError("set!: undefined variable");
    Value val = e->eval(env);
    modify(var, val, env);
    return VoidV();
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }
    
    return VoidV();
}

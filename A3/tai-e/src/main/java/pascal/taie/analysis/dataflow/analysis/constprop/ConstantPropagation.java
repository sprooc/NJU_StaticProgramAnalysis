/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.Map;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact fact = new CPFact();
        for (Var param : cfg.getIR().getParams()) {
            if (canHoldInt(param)) {
                fact.update(param, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((var, value) -> {
            target.update(var, meetValue(value, target.get(var)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isConstant() && v2.isConstant()) {
            if (v1.getConstant() != v2.getConstant()) {
                v2 = Value.getNAC();
            }
        } else if (v1.isNAC() || v2.isNAC()) {
            v2 = Value.getNAC();
        } else if (v1.isConstant()) {
            v2 = v1;
        }
        return v2;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (!(stmt instanceof DefinitionStmt<?, ?>)) {
            return out.copyFrom(in);
        }
        Boolean changed = out.copyFrom(in);
        LValue lValue = ((DefinitionStmt<?, ?>) stmt).getLValue();
        RValue rValue = ((DefinitionStmt<?, ?>) stmt).getRValue();
        if (lValue instanceof Var && canHoldInt((Var) lValue)) {
            changed |= out.update((Var) lValue, evaluate(rValue, in));
        }
        return changed;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        if (exp instanceof Var) {
            return in.get((Var) exp);
        }
        if (exp instanceof BinaryExp) {
            BinaryExp binaryExp = (BinaryExp) exp;
            Var operand1 = binaryExp.getOperand1();
            Var operand2 = binaryExp.getOperand2();
            BinaryExp.Op op = binaryExp.getOperator();
            Value value1 = in.get(operand1);
            Value value2 = in.get(operand2);
            Value outValue = Value.getUndef();
            if (value2.isConstant() && value2.getConstant() == 0) {
                if (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM) {
                    return Value.getUndef();
                }
            }
            if (value1.isConstant() && value2.isConstant()) {
                int num1 = value1.getConstant();
                int num2 = value2.getConstant();
                if (op == ArithmeticExp.Op.ADD) {
                    outValue = Value.makeConstant(num1 + num2);
                } else if (op == ArithmeticExp.Op.SUB) {
                    outValue = Value.makeConstant(num1 - num2);
                } else if (op == ArithmeticExp.Op.MUL) {
                    outValue = Value.makeConstant(num1 * num2);
                } else if (op == ArithmeticExp.Op.DIV) {
                    outValue = Value.makeConstant(num1 / num2);
                } else if (op == ArithmeticExp.Op.REM) {
                    outValue = Value.makeConstant(num1 % num2);
                } else if (op == BitwiseExp.Op.OR) {
                    outValue = Value.makeConstant(num1 | num2);
                } else if (op == BitwiseExp.Op.AND) {
                    outValue = Value.makeConstant(num1 & num2);
                } else if (op == BitwiseExp.Op.XOR) {
                    outValue = Value.makeConstant(num1 ^ num2);
                } else if (op == ShiftExp.Op.SHL) {
                    outValue = Value.makeConstant(num1 << num2);
                } else if (op == ShiftExp.Op.SHR) {
                    outValue = Value.makeConstant(num1 >> num2);
                } else if (op == ShiftExp.Op.USHR) {
                    outValue = Value.makeConstant(num1 >>> num2);
                } else if (op == ConditionExp.Op.EQ) {
                    outValue = Value.makeConstant(num1 == num2 ? 1 : 0);
                } else if (op == ConditionExp.Op.NE) {
                    outValue = Value.makeConstant(num1 != num2 ? 1 : 0);
                } else if (op == ConditionExp.Op.LE) {
                    outValue = Value.makeConstant(num1 <= num2 ? 1 : 0);
                } else if (op == ConditionExp.Op.LT) {
                    outValue = Value.makeConstant(num1 < num2 ? 1 : 0);
                } else if (op == ConditionExp.Op.GE) {
                    outValue = Value.makeConstant(num1 >= num2 ? 1 : 0);
                } else if (op == ConditionExp.Op.GT) {
                    outValue = Value.makeConstant(num1 > num2 ? 1 : 0);
                }
            } else if (value1.isNAC() || value2.isNAC()) {
                outValue = Value.getNAC();
            }
            return outValue;
        }
        return Value.getNAC();
    }
}

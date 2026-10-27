module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.Quasithin.SzN31

namespace SmD6Heis

abbrev M6 : Type := Matrix (Fin 6) (Fin 6) (ZMod 2)

@[expose] def mX : M6 := !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 1, 0]

@[expose] def mY : M6 := !![0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0]

@[expose] def mZ : M6 := !![0, 1, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 1]

@[expose] def mA : M6 := !![0, 1, 1, 1, 0, 1;
    1, 0, 0, 1, 1, 0;
    1, 1, 1, 1, 1, 0;
    0, 1, 0, 1, 1, 1;
    1, 1, 0, 1, 0, 1;
    0, 1, 1, 0, 1, 0]

@[expose] def mB : M6 := !![0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 0]

theorem mA_pow_eight : mA ^ 8 = 1 := by decide +kernel

theorem mA_pow_four_ne : mA ^ 4 ≠ 1 := by decide +kernel

theorem mB_mul_self : mB * mB = 1 := by decide +kernel

theorem mB_mul_mA : mB * mA = mA ^ 3 * mB := by decide +kernel

theorem mA_mul_mX : mA * mX = (mX ^ 1 * mY ^ 1 * mZ ^ 1) * mA := by decide +kernel

theorem mA_mul_mY : mA * mY = (mX ^ 2 * mY ^ 1 * mZ ^ 0) * mA := by decide +kernel

theorem mB_mul_mX : mB * mX = (mX ^ 1 * mY ^ 0 * mZ ^ 2) * mB := by decide +kernel

theorem mB_mul_mY : mB * mY = (mX ^ 0 * mY ^ 2 * mZ ^ 0) * mB := by decide +kernel

end SmD6Heis

end CFSG.Quasithin.SzN31

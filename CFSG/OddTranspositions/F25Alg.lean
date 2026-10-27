module

public import CFSG.OddTranspositions.F25Field
public import CFSG.OddTranspositions.O4Minus5Pair
open CFSG.OddTranspositions.QZ
public section

namespace CFSG.OddTranspositions.QZ

local instance factPrimeFiveAlg : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
noncomputable section

@[expose] def zmodToF25t : ZMod 5 →+* F25t where
  toFun n := ⟨n, 0⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' := by intro a b; rfl
  map_mul' := by
    intro a b
    apply F25t.ext
    · change a * b = a * b + 3 * 0 * 0; ring
    · change (0 : ZMod 5) = a * 0 + 0 * b; ring

instance : SMul (ZMod 5) F25t := ⟨fun n x => zmodToF25t n * x⟩

instance : Module (ZMod 5) F25t where
  smul_add n x y := by
    change zmodToF25t n * (x + y) = zmodToF25t n * x + zmodToF25t n * y
    rw [mul_add]
  add_smul n m x := by
    change zmodToF25t (n + m) * x = zmodToF25t n * x + zmodToF25t m * x
    rw [map_add, add_mul]
  one_smul x := by
    change zmodToF25t 1 * x = x
    rw [map_one, one_mul]
  mul_smul n m x := by
    change zmodToF25t (n * m) * x = zmodToF25t n * (zmodToF25t m * x)
    rw [map_mul, mul_assoc]
  zero_smul x := by
    change zmodToF25t 0 * x = 0
    rw [map_zero, zero_mul]
  smul_zero n := by
    change zmodToF25t n * 0 = 0
    rw [mul_zero]

instance : Algebra (ZMod 5) F25t := Algebra.ofModule'
  (by
    intro r x
    change zmodToF25t r * 1 * x = zmodToF25t r * x
    rw [mul_one])
  (by
    intro r x
    change x * (zmodToF25t r * 1) = zmodToF25t r * x
    rw [mul_one, mul_comm])

noncomputable def algEquiv_F25t : F25t ≃ₐ[ZMod 5] K25 :=
  GaloisField.algEquivGaloisField (p := 5) (n := 2) card_F25t_nat

noncomputable def ringEquiv_F25t : F25t ≃+* K25 :=
  (algEquiv_F25t).toRingEquiv

end

end CFSG.OddTranspositions.QZ

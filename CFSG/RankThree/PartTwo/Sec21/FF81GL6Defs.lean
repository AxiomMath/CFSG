module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.GL6

open Matrix

abbrev G6 : Type := GL (Fin 6) (ZMod 2)

def J0 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0]

def Sp0 : Subgroup G6 where
  carrier := {g | (g : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * J0 * g = J0}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Units.val_mul, transpose_mul] at *
    rw [show b.valᵀ * a.valᵀ * J0 * (a.val * b.val) = b.valᵀ * (a.valᵀ * J0 * a.val) * b.val by
      simp only [Matrix.mul_assoc], ha, hb]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    have h1 : a.val * (a⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (a⁻¹).valᵀ * J0 * (a⁻¹).val
        = (a⁻¹).valᵀ * (a.valᵀ * J0 * a.val) * (a⁻¹).val := by rw [ha]
      _ = (a.val * (a⁻¹).val)ᵀ * J0 * (a.val * (a⁻¹).val) := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = J0 := by rw [h1, transpose_one, Matrix.one_mul, Matrix.mul_one]

def u0M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1]

def u0 : G6 := ⟨u0M, u0M * u0M, by decide, by decide⟩

def u2M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
     1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

def u2 : G6 := ⟨u2M, u2M * u2M, by decide, by decide⟩

def u3M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

def u3 : G6 := ⟨u3M, u3M * u3M, by decide, by decide⟩

def B3 : Subgroup G6 := Subgroup.closure {u0, u2, u3}

def pl : Fin 3 → Fin 6 × Fin 6 := ![(0, 3), (1, 4), (2, 5)]

def Sig (i : Fin 3) : Subgroup G6 where
  carrier := {g | g ∈ Sp0 ∧
    (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Pi.single (pl i).1 1 = Pi.single (pl i).1 1 ∧
    (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Pi.single (pl i).2 1 = Pi.single (pl i).2 1}
  one_mem' := ⟨Sp0.one_mem, by rw [Units.val_one, Matrix.one_mulVec],
    by rw [Units.val_one, Matrix.one_mulVec]⟩
  mul_mem' {a b} ha hb := ⟨Sp0.mul_mem ha.1 hb.1, by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb.2.1, ha.2.1], by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb.2.2, ha.2.2]⟩
  inv_mem' {a} ha := ⟨Sp0.inv_mem ha.1, by
      conv_lhs => rw [← ha.2.1]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec], by
      conv_lhs => rw [← ha.2.2]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]⟩

abbrev Sig0 : Subgroup G6 := Sig 2

def K0 : Subgroup G6 := Sig0 ⊔ Subgroup.zpowers u0

end CFSG.RankThree.PartTwo.Sec21.FF81.GL6

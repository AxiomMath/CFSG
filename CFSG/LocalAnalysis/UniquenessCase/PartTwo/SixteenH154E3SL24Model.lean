module

public import CFSG.GH74.KGroups.FieldGF
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.GH74.KGroups CFSG.Open

abbrev Orth3 : Type := Multiplicative (GF4 × GF4 × GF4)

@[expose] def orth3Act (γ : Matrix.GeneralLinearGroup (Fin 2) GF4) (v : GF4 × GF4 × GF4) :
    GF4 × GF4 × GF4 :=
  (((γ : Matrix (Fin 2) (Fin 2) GF4) 0 0) * v.1 + ((γ : Matrix (Fin 2) (Fin 2) GF4) 0 1) * v.2.1,
   ((γ : Matrix (Fin 2) (Fin 2) GF4) 1 0) * v.1 + ((γ : Matrix (Fin 2) (Fin 2) GF4) 1 1) * v.2.1,
   v.2.2 + (((γ : Matrix (Fin 2) (Fin 2) GF4) 0 0) * ((γ : Matrix (Fin 2) (Fin 2) GF4) 1 0)) ^ 2 *
      v.1 + (((γ : Matrix (Fin 2) (Fin 2) GF4) 0 1) * ((γ : Matrix (Fin 2) (Fin 2) GF4) 1 1)) ^ 2 *
      v.2.1)

@[expose] def orth3L : Subgroup (MulAut Orth3) :=
  Subgroup.closure {σ | ∃ γ ∈ StatedSL 2 GF4,
    ∀ v : Orth3, σ v = Multiplicative.ofAdd (orth3Act γ (Multiplicative.toAdd v))}

@[expose] def orth3Z : Subgroup Orth3 where
  carrier := {v | (Multiplicative.toAdd v).1 = 0 ∧ (Multiplicative.toAdd v).2.1 = 0}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · show (Multiplicative.toAdd a).1 + (Multiplicative.toAdd b).1 = 0
      rw [ha1, hb1]
      decide
    · show (Multiplicative.toAdd a).2.1 + (Multiplicative.toAdd b).2.1 = 0
      rw [ha2, hb2]
      decide
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩
    · show -(Multiplicative.toAdd a).1 = 0
      rw [ha1]
      decide
    · show -(Multiplicative.toAdd a).2.1 = 0
      rw [ha2]
      decide

@[expose] def orth3Phi : MulAut Orth3 where
  toFun v := Multiplicative.ofAdd
    ((Multiplicative.toAdd v).1 ^ 2, (Multiplicative.toAdd v).2.1 ^ 2,
      (Multiplicative.toAdd v).2.2 ^ 2)
  invFun v := Multiplicative.ofAdd
    ((Multiplicative.toAdd v).1 ^ 2, (Multiplicative.toAdd v).2.1 ^ 2,
      (Multiplicative.toAdd v).2.2 ^ 2)
  left_inv v := by
    have h : ∀ x : GF4, (x ^ 2) ^ 2 = x := by decide
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, h]
  right_inv v := by
    have h : ∀ x : GF4, (x ^ 2) ^ 2 = x := by decide
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, h]
  map_mul' a b := by
    have h : ∀ x y : GF4, (x + y) ^ 2 = x ^ 2 + y ^ 2 := by decide
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, h]
    rfl

@[expose] def orth3Scal (μ : GF4) (hμ : μ ≠ 0) : MulAut Orth3 where
  toFun v := Multiplicative.ofAdd
    (μ * (Multiplicative.toAdd v).1, μ * (Multiplicative.toAdd v).2.1,
      μ * (Multiplicative.toAdd v).2.2)
  invFun v := Multiplicative.ofAdd
    (μ⁻¹ * (Multiplicative.toAdd v).1, μ⁻¹ * (Multiplicative.toAdd v).2.1,
      μ⁻¹ * (Multiplicative.toAdd v).2.2)
  left_inv v := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, inv_mul_cancel_left₀ hμ]
  right_inv v := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, mul_inv_cancel_left₀ hμ]
  map_mul' a b := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, mul_add]
    rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

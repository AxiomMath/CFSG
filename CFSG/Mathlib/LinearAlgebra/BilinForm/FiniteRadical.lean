module

public import CFSG.Mathlib.LinearAlgebra.BilinForm.Reflection
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness

public section

namespace LinearMap.BilinMap

variable {V W : Type*} [AddCommGroup V] [Module (ZMod 3) V]
  [AddCommGroup W] [Module (ZMod 3) W]

theorem eq_zero_of_card_le_three_mul_card_mul_card [Finite V]
    (b : V →ₗ[ZMod 3] V →ₗ[ZMod 3] W) (hb : b.IsAlt)
    (K S : AddSubgroup V) (hK : K ≤ b.ker.toAddSubgroup)
    (hS : S ≤ b.ker.toAddSubgroup) (hKS : K ⊓ S = ⊥)
    (hcard : Nat.card V ≤ 3 * (Nat.card K * Nat.card S)) :
    b = 0 := by
  classical
  have hker : Nat.card K * Nat.card S ≤ Nat.card b.ker := by
    let f : K × S → b.ker := fun p =>
      ⟨(p.1 : V) + (p.2 : V),
        b.ker.toAddSubgroup.add_mem (hK p.1.2) (hS p.2.2)⟩
    have hf : Function.Injective f := by
      intro p q hpq
      exact AddSubgroup.add_injective_of_disjoint (disjoint_iff.mpr hKS)
        (congrArg Subtype.val hpq)
    calc Nat.card K * Nat.card S = Nat.card (K × S) := (Nat.card_prod K S).symm
      _ ≤ Nat.card b.ker := Nat.card_le_card_of_injective f hf
  have hVcard : Nat.card V = Nat.card b.ker * Nat.card b.range := by
    calc Nat.card V = Nat.card b.ker * Nat.card (V ⧸ b.ker) :=
          Submodule.card_eq_card_quotient_mul_card b.ker
      _ = Nat.card b.ker * Nat.card b.range := by
          rw [Nat.card_congr (LinearMap.quotKerEquivRange b).toEquiv]
  by_contra hne
  have hfin : 2 ≤ Module.finrank (ZMod 3) b.range :=
    two_le_finrank_range_of_isAlt b hb hne
  have h9 : 9 ≤ Nat.card b.range := by
    have hpow : Nat.card b.range = 3 ^ Module.finrank (ZMod 3) b.range := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod]
    rw [hpow]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ Module.finrank (ZMod 3) b.range :=
          Nat.pow_le_pow_right (by norm_num) hfin
  have hkerpos : 0 < Nat.card b.ker := by
    haveI : Nonempty b.ker := ⟨⟨0, by simp⟩⟩
    haveI : Finite b.ker := Subtype.finite
    exact Nat.card_pos
  have hle : Nat.card b.ker * Nat.card b.range ≤ 3 * Nat.card b.ker := by
    calc Nat.card b.ker * Nat.card b.range = Nat.card V := hVcard.symm
      _ ≤ 3 * (Nat.card K * Nat.card S) := hcard
      _ ≤ 3 * Nat.card b.ker := Nat.mul_le_mul_left 3 hker
  have hge : Nat.card b.ker * 9 ≤ Nat.card b.ker * Nat.card b.range :=
    Nat.mul_le_mul_left _ h9
  omega

end LinearMap.BilinMap

end

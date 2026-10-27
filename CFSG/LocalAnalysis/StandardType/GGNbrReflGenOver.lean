module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Over

variable {G : Type} [Group G] {Bs K : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (K : Set G))

@[expose] def GGOverGamma (c : MulAut ↥Bs) (a : MulAut ↥(ggGamma K hN).range) : Prop :=
  ∀ b : ↥Bs, (ggGamma K hN).rangeRestrict (c b) = a ((ggGamma K hN).rangeRestrict b)

variable {hN}

theorem GGOverGamma.one : GGOverGamma hN (1 : MulAut ↥Bs) 1 := fun _ => rfl

theorem GGOverGamma.mul {c₁ c₂ : MulAut ↥Bs} {a₁ a₂ : MulAut ↥(ggGamma K hN).range}
    (h₁ : GGOverGamma hN c₁ a₁) (h₂ : GGOverGamma hN c₂ a₂) :
    GGOverGamma hN (c₁ * c₂) (a₁ * a₂) := by
  intro b
  rw [MulAut.mul_apply, MulAut.mul_apply, h₁ (c₂ b), h₂ b]

theorem GGOverGamma.inv {c : MulAut ↥Bs} {a : MulAut ↥(ggGamma K hN).range}
    (h : GGOverGamma hN c a) : GGOverGamma hN c⁻¹ a⁻¹ := by
  intro b
  have h1 := h (c⁻¹ b)
  rw [MulAut.apply_inv_self] at h1
  rw [h1, MulAut.inv_apply_self]

theorem GGOverGamma.pow {c : MulAut ↥Bs} {a : MulAut ↥(ggGamma K hN).range}
    (h : GGOverGamma hN c a) (k : ℕ) : GGOverGamma hN (c ^ k) (a ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact GGOverGamma.one
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h

theorem ggOverGamma_conjAut {g : G} (hgK : g ∈ K) (hg : g ∈ Subgroup.normalizer (Bs : Set G)) :
    GGOverGamma hN (ggConjAut Bs hg)
      (ggConjAut (ggGamma K hN).range (conj_mem_normalizer_range_ggGamma hN hgK hg)) := by
  intro b
  have hb := (ggConjAut Bs hg b).2
  apply Subtype.ext
  exact ggGamma_conj K hN (⟨g, hgK⟩ : K) b hb

theorem GGOverGamma.eq_one_of_one {a : MulAut ↥(ggGamma K hN).range}
    (h : GGOverGamma hN (1 : MulAut ↥Bs) a) : a = 1 := by
  refine MulEquiv.ext fun s => ?_
  obtain ⟨b, rfl⟩ := (ggGamma K hN).rangeRestrict_surjective s
  have hb := h b
  rw [MulAut.one_apply] at hb
  exact hb.symm

end Over

theorem GGOverGamma.unique {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    {hN : Bs ≤ Subgroup.normalizer (K : Set G)} {c : MulAut ↥Bs}
    {a a' : MulAut ↥(ggGamma K hN).range} (h : GGOverGamma hN c a)
    (h' : GGOverGamma hN c a') : a = a' := by
  have h1 := h.inv.mul h'
  rw [inv_mul_cancel] at h1
  have h2 := GGOverGamma.eq_one_of_one h1
  rw [← mul_left_cancel_iff (a := a), mul_one, ← mul_assoc, mul_inv_cancel, one_mul] at h2
  exact h2.symm

end CFSG.StandardType

end

module

public import CFSG.RankThree.GF2n.Stroth80.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80.FieldModel

open scoped commutatorElement Matrix
open Polynomial CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim79

variable {G : Type} [Group G]

theorem scalars_of_centralizes {K : Type} [Field K] {γ : G → K} {Z : Subgroup G}
    (hsurj : ∀ s : K, ∃ a ∈ Z, γ a = s) {m : G} {σ : K ≃+* K} {a : K}
    (h : ∀ z ∈ Z, γ (m * z * m⁻¹) = a * σ (γ z)) (hc : ∀ z ∈ Z, m * z * m⁻¹ = z) :
    a = 1 ∧ σ = RingEquiv.refl K := by
  have h1 : a = 1 := by
    obtain ⟨z, hz, hz1⟩ := hsurj 1
    have := h z hz
    rw [hc z hz, hz1, map_one, mul_one] at this
    exact this.symm
  refine ⟨h1, RingEquiv.ext fun s => ?_⟩
  obtain ⟨z, hz, rfl⟩ := hsurj s
  have := h z hz
  rw [hc z hz, h1, one_mul] at this
  exact this.symm

end CFSG.RankThree.GF2n.Stroth80.FieldModel

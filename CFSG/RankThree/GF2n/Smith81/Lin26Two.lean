module

public import CFSG.RankThree.GF2n.Smith81.Lin26TwoModule

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Pointwise Matrix

section TwoRoots

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {V₁ V₂ : Subgroup G}

theorem LinSetup.exists_roots_two (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂)
    (hBV : B ≤ V₁) :
    (∃ Y : Subgroup G, Ctx M Q Z Y ∧ Y ≤ V₁ ∧ V₁ ≤ QB Y) ∧
      ∃ Y : Subgroup G, Ctx M Q Z Y ∧ Y ≤ V₂ ∧ V₂ ≤ QB Y := by
  have hmod := LinSetup.le_QB_two hc hS hBV
  refine ⟨⟨B, hc, hBV, hmod⟩, ?_⟩
  obtain ⟨x, hxM, hx⟩ := hS.exists_swap
  refine ⟨conjSubgroup x B, hc.conj_of_mem hxM, ?_, ?_⟩
  · rw [← hx]
    intro y hy
    rw [mem_conjSubgroup] at hy ⊢
    exact hBV hy
  · rw [QB_conj, ← hx]
    intro y hy
    rw [mem_conjSubgroup] at hy ⊢
    exact hmod hy

end TwoRoots

section Main


theorem lin26Scalar_of_two (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G)
    (V₁ V₂ : Subgroup G) (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B 2 V₁ V₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ ∧
      ∃ c ∈ M, ∃ ν : Kˣ, ν ≠ 1 ∧ ∀ x ∈ Q, M₀.π (c * x * c⁻¹) = (ν : K) • M₀.π x := by
  obtain ⟨V₁', V₂', hS', hBV, h31⟩ := lin31Statement_holds G M Q Z B 2 V₁ V₂ hb hc hS le_rfl
  obtain ⟨R, hsl⟩ := exists_restModel_sl_two hc hS'
  obtain ⟨hroot₁, hroot₂⟩ := LinSetup.exists_roots_two hc hS' hBV
  obtain ⟨c, hcM, ν, hν, hcπ⟩ := R.exists_scalar le_rfl hsl h31 hroot₁ hroot₂
  exact ⟨R.K, R.instField, R.instFinite, R.instChar, R.γ, R.M₀, R.gm, c, hcM, ν, hν, hcπ⟩

end Main

end CFSG.RankThree.GF2n.Smith81

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Certified


theorem mBar_le_bBar_add_of_delta (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) {L : Subgroup G} (k₀ : ℕ)
    (hLM : CFSG.Open.IsSubnormal L D.M) (hLq : CFSG.Open.IsQuasisimple (UC22.Bar2 L))
    (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥)
    (hU : UniqueMax D.M (UC22.conjClosure D.M L))
    (hconf : V₀ ≠ ⊥ → ∃ Δ : Finset (Subgroup G),
      (∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M) ∧ UniqueMax D.M (⨆ H ∈ Δ, H) ∧
      (∀ H ∈ Δ, CFSG.LocalAnalysis.WeakClosure81.InFSq 2 H) ∧
      (∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g))
    (hk : D.k ≤ k₀) :
    mBar D.M V₀ V hV.isElemAbelian ≤
      bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian + k₀ + 2 := by
  by_cases hV0 : V₀ = ⊥
  · have h1 := twelve_twentyThree_one D hx h61 h126 h111 hV hV0 hLM hLq hL1 hU
    omega
  · obtain ⟨Δ, hTM, hUΔ, hι, hO2⟩ := hconf hV0
    set ι : Subgroup G → ℕ := fun _ => 2 with hιdef
    have hsup : Δ.sup ι ≤ 2 := by
      by_cases hne : Δ.Nonempty
      · exact Finset.sup_le fun H _ => by simp [hιdef]
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        simp [hne]
    have h3 := twelve_twentyThree_three D hx h61 h127 h1114 h162 hTor h1482 h126 hV hV0
      hLM hLq hL1 hTM hUΔ ι (fun H hH => hι H hH) hO2
    have h4 : Δ.sup ι ≤ 2 := hsup
    omega

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

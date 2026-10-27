module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestSetup

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms

theorem ggSporKRest_false_of_cover {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat p H E) (hK : ¬ CFSG.generalizedFitting W ≤ H)
    (hOut : Nat.card (Outer ↥(CFSG.generalizedFitting W)) ≤ 2)
    (hCov : SporKRestCover p ↥(CFSG.generalizedFitting W)) : False := by
  obtain ⟨_, hEab, hE2, ⟨S, hSH⟩, hctl⟩ := ggSporKRest_setup hyp hOut
  obtain ⟨x, hxE, hx1, hgen⟩ := hCov (E.subgroupOf (CFSG.generalizedFitting W)) hEab hE2
  have hHF : H.subgroupOf (CFSG.generalizedFitting W) = ⊤ :=
    hgen (H.subgroupOf (CFSG.generalizedFitting W)) ⟨S, hSH⟩ (hctl x hxE hx1)
  refine hK (fun f hf => ?_)
  have hx : (⟨f, hf⟩ : ↥(CFSG.generalizedFitting W)) ∈
      H.subgroupOf (CFSG.generalizedFitting W) := by
    rw [hHF]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hx

end CFSG.StandardType.SporadicShape

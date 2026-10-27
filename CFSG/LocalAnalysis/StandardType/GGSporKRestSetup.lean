module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestSylow
public import CFSG.LocalAnalysis.StandardType.GGSporKRestFStar
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms

theorem ggSporKRest_setup {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat p H E)
    (hOut : Nat.card (Outer ↥(CFSG.generalizedFitting W)) ≤ 2) :
    E ≤ CFSG.generalizedFitting W ∧
      IsElemAbelian p (E.subgroupOf (CFSG.generalizedFitting W)) ∧
      Nat.card (E.subgroupOf (CFSG.generalizedFitting W)) = p ^ 2 ∧
      (∃ S : Sylow p ↥(CFSG.generalizedFitting W),
        (S : Subgroup ↥(CFSG.generalizedFitting W)) ≤ H.subgroupOf (CFSG.generalizedFitting W)) ∧
      SporKRestControls (E.subgroupOf (CFSG.generalizedFitting W))
        (H.subgroupOf (CFSG.generalizedFitting W)) := by
  obtain ⟨⟨hp, hp2, hE, hE2, hctl⟩, -⟩ := hyp
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hEF : E ≤ CFSG.generalizedFitting W := by
    intro e he
    exact ggSporKRest_mem_fstar_of_pow_eq_one hpodd hOut (hE.2 e he)
  have hEabF : IsElemAbelian p (E.subgroupOf (CFSG.generalizedFitting W)) :=
    CFSG.Open.IsElemAbelian.subgroupOf hE (CFSG.generalizedFitting W)
  refine ⟨hEF, hEabF, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEF).toEquiv, hE2]
  · obtain ⟨P, _hEP, hPH⟩ := ggSporKRest_sylow_le hp hE hE2 hctl
    have hPF : (P : Subgroup W) ≤ CFSG.generalizedFitting W :=
      ggSporKRest_pGroup_le_fstar hpodd hOut P.isPGroup'
    exact ggSporKRest_sylow_subgroupOf P hPF hPH
  · exact ggSporKRest_controls_subgroupOf hctl

end CFSG.StandardType.SporadicShape

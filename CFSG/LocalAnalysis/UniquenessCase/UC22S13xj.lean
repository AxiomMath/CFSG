module

import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IrrOnMod)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem uc22s13xj_isSylowOf_of_inf {p : ℕ} [Fact p.Prime] {M H P : Subgroup G}
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M)
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M)) (hP1 : P ≠ ⊥) :
    CFSG.ABGLocalTools.IsSylowOf p P H := by
  have hPH : P ≤ H := hP.le.trans inf_le_left
  obtain ⟨S, hS⟩ := (hP.isPGroup.comap_subtype (K := H)).exists_le_sylow
  have hQ : CFSG.ABGLocalTools.IsSylowOf p ((S : Subgroup ↥H).map H.subtype) H := ⟨S, rfl⟩
  have hPQ : P ≤ (S : Subgroup ↥H).map H.subtype := fun x hx =>
    ⟨⟨x, hPH hx⟩, hS (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hQM : (S : Subgroup ↥H).map H.subtype ≤ M := by
    refine hM.le_of_isPGroup_inf hQ.isPGroup fun h => hP1 (eq_bot_iff.2 fun x hx => ?_)
    rw [← h]
    exact ⟨hPQ hx, (Subgroup.mem_inf.1 (hP.le hx)).2⟩
  rw [← hP.eq_of_le hPQ (le_inf hQ.le hQM) hQ.isPGroup]
  exact hQ

end CFSG.LocalAnalysis.UniquenessCase.UC22

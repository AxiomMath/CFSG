module

import CFSG.GroupTheory.PRankLeOfSylowLe
import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48Tail
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericFixedPoints
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.S2251

open Subgroup

theorem pSubgroups_le_of_cyclic {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {D H : Subgroup X} [D.Normal] (hDH : D ≤ H)
    (hrank : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X))
    (hidx : ∀ P : Subgroup X, IsPGroup p P → D.relIndex P ≤ p)
    (hcyc : ∀ P : Subgroup X, P ≤ H → IsPGroup p P → IsCyclic P) :
    ∀ P : Subgroup X, P ≤ H → IsPGroup p P → P ≤ D := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro P hPH hP
  by_contra hPD
  obtain ⟨R, hR, hPR⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.exists_isSylowOf_ge_of_isPGroup
    (le_top : P ≤ ⊤) hP
  have hDR : R ⊓ D ≤ R ⊓ H := inf_le_inf_left _ hDH
  have hHP : ¬ R ⊓ H ≤ R ⊓ D := fun h => hPD ((le_inf hPR hPH).trans h |>.trans inf_le_right)
  have hRH : R ≤ H :=
    (CFSG.StandardType.GGL48.le_of_relIndex_le_prime hDR inf_le_left hR.isPGroup
      (by rw [Subgroup.inf_relIndex_left]; exact hidx R hR.isPGroup) hHP).trans inf_le_right
  have hcR : IsCyclic R := hcyc R hRH hR.isPGroup
  have hbound := CFSG.pRank_le_of_isSylowOf_le hp hR.le hR (le_refl R)
  have hRrank := CFSG.SectionRank.pRank_le_one_of_isCyclic hp hcR
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.S2251

module

public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4SmallProof
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGFixLocal

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace SmallKG

theorem ggD4TwoLocalThree_omegaPlus {K : Type} [Field K] [CharP K 2] :
    GGD4TwoLocalThree (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) := by
  obtain ⟨hW2, hW1, -, hWE⟩ := zpowers_facts (φ := 1) (E := (L45Fix.torusR K).range)
    L45Fix.invR_sq L45Fix.invR_ne_one rfl (by
      rintro _ ⟨x, rfl⟩
      exact (L45Fix.commute_torusR_invR x).eq)
  exact ⟨_, _, L45Fix.isElemAbelian_range_m3 _, L45Fix.card_range_m3 L45Fix.torusR_injective,
    hW2, hW1, hWE⟩

end SmallKG

open SmallKG

theorem ggD4TwoLocalThree_labelAll (lab : LargeEvenLabel) (ht : lab.tag = .D)
    (h4 : lab.rank = 4) : LargeEvenLabelAll lab GGD4TwoLocalThree := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h4
  subst h4
  exact largeEvenLabelAll_omegaPlus ht le_rfl fun _ _ _ _ _ => ggD4TwoLocalThree_omegaPlus

theorem ggD4TwoLocalThreeOddInput_holds : GGD4TwoLocalThreeOddInput :=
  fun lab _ ht h4 _ => ggD4TwoLocalThree_labelAll lab ht h4

end CFSG.StandardType

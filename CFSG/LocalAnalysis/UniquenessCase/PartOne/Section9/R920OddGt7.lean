module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Inputs
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddFermat
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddJ1
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddLie
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddUni

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem false_of_hN_gt_seven (S : Slice D L D₃ Y H q) (hq : 7 < q)
    (hN : ∀ A : Subgroup G, A ≤ Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M)
    {E : Subgroup G} (hyp : F09.Hyp91 D Y H E)
    (hK32 : UCK.K32) (hK461 : UCK.K461) (hK462 : UCK.K462)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hZ : UCK.ZassenhausPerfect) : False := by
  have hI := S.I9_le_M hN hyp hK461 hK462 hSch hZ
  rcases S.lieChar_or_J1 hq hyp hK32 with hchev | ⟨h11, hJ1⟩
  · exact S.false_of_lieChar hq hN hyp hI hchev hGA
  · exact S.not_isSpor_J1_Lbar9 hN hyp hI h11 hSp hJ1

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

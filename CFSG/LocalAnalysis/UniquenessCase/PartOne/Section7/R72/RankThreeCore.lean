module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.OfCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ReeU3Excl
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.ReeThreeType

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)

variable {G : Type} [Group G] [Finite G]


theorem r72_dataOfSetup_of (hId : CFSG.AGLEmbedding.KFactSmallIdent)
    (hLie : CFSG.AGLEmbedding.KFactOneLieIdent)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hOutP : CFSG.AGLEmbedding.KFactSmallOutPPrime)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hSE : StronglyEmbeddedFive)
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hS : CFSG.LocalAnalysis.RankThreeUC.Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : CFSG.LocalAnalysis.RankThreeUC.AGL81TheoremC G)
    (S : CFSG.LocalAnalysis.RankThreeUC.Setup G) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F07.R72
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three.dataOfSetup hS S) := by
  intro p H h7
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal p h7.1 h7.2.1 h7.2.2.1
    (PartTwo.Three.normalizer_le_of_agl81TheoremC hUC hC S h7.1 h7.2.1 h7.2.2.1)
  have hH : k.Config H := config_of_sec7Hyp k h7 rfl
  exact r72_of_core hId hLie hCyc hOutP hbr (fun _ _ _ => isReeType_one_of_psl28) k
    (fun hp5 => ⟨k.kIDExcluded_of_evenRank_le_three (le_of_eq hS.rank), k.step75 hp5 hSE⟩) hH
    (fun hp3 => k.exists_rows3_of_config hG3 hRee hp3 hH)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72

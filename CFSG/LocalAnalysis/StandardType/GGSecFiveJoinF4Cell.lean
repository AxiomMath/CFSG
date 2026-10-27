module

public import CFSG.LocalAnalysis.StandardType.GGF4JoinA3CommonPair
public import CFSG.LocalAnalysis.StandardType.GGF4JoinB3Guarded
import CFSG.LocalAnalysis.StandardType.GGF4OriginalTypes
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberPSL
import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinF4
import CFSG.Open.LocalVocabulary
import CFSG.LieType.Chevalley.E6GraphInvolutionForms
import CFSG.RankThree.PartOne.KE.E7ThreeA1
import CFSG.Blueprint.ChevalleyRootArtifact
import CFSG.LocalAnalysis.SeitzReduction.E8PilotLeviHom
import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
import CFSG.LocalAnalysis.StandardType.GGExcFieldRankE7
import CFSG.LocalAnalysis.StandardType.GGSecFiveF4ReflMax
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.SpTwoLocalRankLower
import CFSG.LieType.SeitzGeneration.ExcTorusRank
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedPSU
import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedSpMember
import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberE8
import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberE6
import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberTwistedE6
import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedOmegaMinus
import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberPOmegaPlus
import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedF4
import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggSecFiveCompatJoinResNAt_F4_of_member (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hSmall : GGSecFiveF4SmallLabelInput) (hExcl : GGSecFiveF4SmallExclusionInput)
    (hMem : ∀ t, GGF4JoinMemberAt t) : GGSecFiveCompatJoinResNAt GGIsWeylMatrixF4 :=
  ggSecFiveCompatJoinResNAt_F4_of_leaves hTBF hWI
    (ggSecFiveF4OriginalTypesInput_holds hX hTCJ ggLabelRigidInput_holds hTBF hWI) hSmall hExcl
    (ggF4JoinA3ProperInput_of_jRefl hX hTCJ ggLabelRigidInput_holds hTBF hWI hTPn hA8
      ggRawInnFieldInput_holds hiso hFC hL hP (ggF4JoinJReflA2Input_holds hTBF hWI))
    (ggF4JoinB3GuardedInput_of_inputs hTBF hWI) hMem

theorem ggSecFiveCompatJoinResNAt_F4_of_tags
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hSmall : GGSecFiveF4SmallLabelInput) (hExcl : GGSecFiveF4SmallExclusionInput) :
    GGSecFiveCompatJoinResNAt GGIsWeylMatrixF4 :=
  ggSecFiveCompatJoinResNAt_F4_of_member hTBF hWI hX hTCJ hTPn hA8 hiso hFC hL hP hSmall hExcl
    (fun t => ggF4JoinMemberAt_of_known knownActualMemberSelectedInput_holds t)

end CFSG.StandardType

end

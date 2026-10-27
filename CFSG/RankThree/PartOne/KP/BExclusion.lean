module

public import CFSG.RankThree.PartOne.KP.CoverEmbedding
public import CFSG.RankThree.PartOne.KP.BData
public import CFSG.Monster.B.CTIB.UniqueComponent
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3175
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16040
public import Certificates.Certificate113
public import Certificates.Certificate3027
public import Certificates.Certificate3082
public import Certificates.Certificate114
public import Certificates.Certificate3014
public import Certificates.Certificate3083
public import Certificates.Certificate117
public import Certificates.Certificate16951
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate45
public import Certificates.Certificate3025
public import Certificates.Certificate46
public import Certificates.Certificate3026
public import Certificates.Certificate47
public import Certificates.Certificate3028
public import Certificates.Certificate48
public import Certificates.Certificate3045
public import Certificates.Certificate49
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
open CFSG.LieType.Chevalley.C2E6Std
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem exists_quasisimple_in_centralizer_labelS :
    ∃ K : Subgroup (Subgroup.centralizer ({labelS} : Set Sbp)), IsQuasisimple K ∧
      Nat.card (Subgroup.center K) = 2 ∧ Nonempty (K ⧸ Subgroup.center K ≃* stdGroup) := by
  obtain ⟨-, hperf, -, hcen, hc2, ⟨θ⟩, -, hcard⟩ := derivedCoverInput_holds
  have hs' := @MulEquiv.isSimpleGroup _ _ _ _ stdGroup_simple θ
  have hq := isQuasisimple_of_cover hperf hcen hc2 hs' (by rw [hcard]; norm_num)
  have hz := card_center_commutator hcen hc2
  obtain ⟨ι, hι⟩ := exists_embedding_into_centralizer Shat Eam Eam_le_Shat sEquiv labelS cS
    sEquiv_labelS (fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (Eam_le_centralizer hx))
  exact exists_quasisimple_range_of_injective (ι.comp (commutator Eam).subtype)
    (hι.comp (commutator Eam).subtype_injective) hq hz
    ((QuotientGroup.quotientMulEquivOfEq (center_commutator_eq hcen)).trans θ)

theorem bMonsterData_Sbp : BMonsterData Sbp := by
  obtain ⟨K, hq, hz, hQ⟩ := exists_quasisimple_in_centralizer_labelS
  exact ⟨labelS, K, hq, hz, hQ⟩

theorem sectionsForceEvenRankFour_B : SectionsForceEvenRankFour (Carrier .B) :=
  sectionsForceEvenRankFour_B_of_monsterData iotaEquiv bMonsterData_Sbp

end CFSG.RankThree.PartOne

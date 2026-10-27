module

public import CFSG.LocalAnalysis.WeakClosure81.W183Cited
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFive
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22SemiMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem asch2_2One_of_kfact (hC5 : CFSG.AGLEmbedding.KFactCoverRankFive) : Asch2_2One := by
  intro Q _ _ G p hp hp3 hK hrk M N _ hNM hMG hE
  have hp5 : 5 ≤ p := by
    have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    omega
  have hrk' : CFSG.Open.pRank p (⊤ : Subgroup ↥G) ≤ 3 := by
    rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup G] at hrk
  let e : ↥(M.subgroupOf G) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hMG
  let π : ↥(M.subgroupOf G) →* ↥M ⧸ N.subgroupOf M :=
    (QuotientGroup.mk' (N.subgroupOf M)).comp e.toMonoidHom
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective (N.subgroupOf M)).comp e.surjective
  exact Asch22.pRank_le_three_of_layer_eq_top hC5 (G := ↥G) hK hp hp5 hrk'
    (M.subgroupOf G) π hπ hE

theorem asch2_2One_of_tables
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) : Asch2_2One :=
  asch2_2One_of_kfact (CFSG.AGLEmbedding.kFactCoverRankFive_of hGA hSpor)

end CFSG.LocalAnalysis.WeakClosure81

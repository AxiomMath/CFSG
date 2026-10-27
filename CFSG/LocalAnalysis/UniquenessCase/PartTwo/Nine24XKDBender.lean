module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LargeExtraspecial.S8CBFSmall
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Over

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Blueprint (LieModel)

theorem eq_top_of_normalized_by_sylow_of_bender {L : Type} [Group L] [Finite L]
    (hB : CFSG.Open.fusionIsBenderGroup L) {T X : Subgroup L}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hX : X ≠ ⊥) (hXperf : ⁅X, X⁆ = X)
    (hTX : T ≤ normalizer (X : Set L)) : X = ⊤ := by
  haveI hsimple : IsSimpleGroup L :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  have hsup : X ⊔ T = ⊤ := by
    by_contra hne
    have hT2 : IsPGroup 2 T := hT.isPGroup
    have hIdx : ¬ 2 ∣ T.index := by
      rw [← Subgroup.relIndex_top_right]
      exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.2
    let Q : Sylow 2 L := hT2.toSylow hIdx
    have hQT : (Q : Subgroup L) = T := IsPGroup.toSylow_coe hT2 hIdx
    have hQM : (Q : Subgroup L) ≤ X ⊔ T := by
      rw [hQT]
      exact le_sup_right
    have hsolv : Group.IsSolvable ↥(X ⊔ T) :=
      CFSG.QuasithinUnique.Unc25G2.A312Sub.bender_overgroups hB Q hQM hne
    haveI : Group.IsSolvable ↥(X ⊔ T) := hsolv
    have hXsolv : Group.IsSolvable ↥X :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_sup_left : X ≤ X ⊔ T))
        (Subgroup.inclusion_injective _)
    haveI : Group.IsPerfect X := Subgroup.isPerfect_iff.mpr hXperf
    haveI : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX
    exact Group.IsPerfect.not_isSolvable X hXsolv
  have hnorm : (X : Subgroup L).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact eq_top_iff.mpr (hsup ▸ sup_le Subgroup.le_normalizer hTX)
  haveI : (X : Subgroup L).Normal := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X with hbot | htop
  · exact (hX hbot).elim
  · exact htop

theorem fusionIsBenderGroup_of_isL2_two {L : Type} [Group L] {f : ℕ} (hL : IsL2 L f) :
    CFSG.Open.fusionIsBenderGroup L := by
  exact CFSG.LargeExtraspecial.S8.fusionIsBenderGroup_of_lieModel_psl_two hL

theorem fusionIsBenderGroup_of_isU3_two {L : Type} [Group L] {f : ℕ} (hL : IsU3 L f) :
    CFSG.Open.fusionIsBenderGroup L := by
  exact CFSG.LargeExtraspecial.S8.fusionIsBenderGroup_of_lieModel_psu_three hL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

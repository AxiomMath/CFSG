module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derModel
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derJData
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derCardB
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derThree
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derBetaRange
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derBetaKer
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derUBar
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derRank
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derIsoPlane
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derSixFix
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derPrePair
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derSmall
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derExistsY

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggConfig_not_B2der_of_model {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    (hJ : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hmodel : ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (r : ℕ) (_ : NeZero r),
      Nat.card K = 2 ∧ 3 ≤ r ∧
      ∃ (ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K r))
        (β : ↥B →* LargeEvenProj (LargeEvenSpGroup K r)),
        GGB2derModelProp B L hBL ψ β ∧ ∀ y : ↥B, (y : G) ∈ D → (y : G) ∉ Subgroup.zpowers x →
          IsPGroup 2 (Subgroup.center ↥L) ∧ (4 ≤ r → Subgroup.center ↥L = ⊥) ∧
            Module.finrank K
              (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (β y))) = 4 ∧
            (J.subgroupOf L).map ψ =
              ⁅ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (β y))),
                ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (β y)))⁆) :
    False := by
  classical
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType 3 B x L := hcfg.1.2.2.2.2.2.2.2
  have hpre : LargeEvenStdSubPre 3 B x L D J := hcfg.2.2.1
  have hclause := hcfg.2.2.2
  have hB : IsElemAbelian 3 B := hS.1.1
  have hxB : x ∈ B := hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  obtain ⟨hxL, -, hx3, hperf⟩ := GGConfig.data_L hcfg
  have hcyc := hS.2.2.2.2
  have hDB : D ≤ B := hpre.1
  have hDcard : Nat.card D = 3 ^ 2 := hpre.2.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hpre.2.2.2.2.2.1
  have hDcent : D = B ⊓ Subgroup.centralizer (J : Set G) := hpre.2.2.2.2.2.2
  have hJL : J ≤ L := hcomp.1.trans inf_le_left
  have hJperf : commutator ↥J = ⊤ := hcomp.2.2.1
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := le_normalizer_of_stdSub hS hst hpre
  have h81 : Nat.card B = 81 := ggB2der_card_B hcfg hJ
  have hrank : LargeEvenTwoLocalRank 3 G ≤ 4 := by
    have h := GGConfig.card_B_eq hcfg
    rw [h81] at h
    have : (3 : ℕ) ^ LargeEvenTwoLocalRank 3 G = 3 ^ 4 := by rw [← h]; norm_num
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) this).le
  obtain ⟨K, _, _, _, r, _, hK, hr3, ψ, β, hM, hdata⟩ := hmodel
  obtain ⟨y, hyD, hyx, hDxy⟩ := ggB2der_exists_y hB hDB hDcard hxD hx1
  obtain ⟨hZ2, hZ1, hW4, hψJ⟩ := hdata y hyD hyx
  obtain ⟨hkerβ, hEab, hEc⟩ := ggB2der_beta_range hK hr3 hM hperf hB hxB hx1 hxL hcyc h81
  obtain ⟨S, hSJ, hS3, hSnc⟩ := ggB2der_noncyclic_three hJ
  obtain ⟨U, hU1, hU2, hEU⟩ := ggB2der_U_bar hcfg hK hr3 hM hZ2 ⟨S, hSJ.trans hJL, hS3, hSnc⟩
  have hr4 : 4 ≤ r := ggB2der_four_le_rank hK hEab hEc hU1 hU2 hEU
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hr4' : r ≤ 4 := ggB2der_rank_le_four hK hr3 hM.surj hM.ker_eq hperf hLx hx1 hx3 hrank
  have hr : r = 4 := le_antisymm hr4' hr4
  subst hr
  have hker0 : ψ.ker = ⊥ := by rw [hM.ker_eq]; exact hZ1 le_rfl
  have hψinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hker0
  have hzE : β y ∈ β.range := ⟨y, rfl⟩
  have hz3 : (β y) ^ 3 = 1 := hEab.2 _ hzE
  have hβx : ∀ b : ↥B, (b : G) ∈ Subgroup.zpowers x → β b = 1 := by
    intro b hb
    rw [← hkerβ] at hb
    obtain ⟨b', hb', hbb'⟩ := Subgroup.mem_map.mp hb
    have : b' = b := Subtype.ext hbb'
    rw [← this]
    exact hb'
  have hz1 : β y ≠ 1 := by
    intro h
    have hy : (y : G) ∈ β.ker.map B.subtype := ⟨y, h, rfl⟩
    rw [hkerβ] at hy
    exact hyx hy
  have hdim8 : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hB_alt : (SmallRule.spBilin K 4).IsAlt :=
    CFSG.ClassicalGroups.Symplectic.spForm_isAlt (m := 4) (K := K)
  have halt : ∀ v, SmallRule.spBilin K 4 v v = 0 := fun v => hB_alt v
  obtain ⟨hcompl, -, -, -⟩ := ggB2der_fix_orth_decomp hK SmallRule.spRep (SmallRule.spBilin K 4)
    SmallRule.spBilin_nondegenerate SmallRule.spBilin_isRefl SmallRule.spRep_isometry hz3
  have hker := ggB2der_hker hK hr3 hM hJL hJperf hBJ hDB hDcent hβx hDxy hyD hcompl hψJ
  obtain ⟨-, T, hT2, hTiso, hTE, hTW⟩ := ggB2der_no_fixed_isotropic_plane hK SmallRule.spRep
    SmallRule.spRep_injective (SmallRule.spBilin K 4) SmallRule.spBilin_nondegenerate
    SmallRule.spBilin_isRefl halt SmallRule.spRep_isometry hdim8 hEab hEc hzE hz1 hW4 hker hU1 hU2
    hEU
  obtain ⟨e, heE, he1, he6, hkere⟩ := ggB2der_six_dim_fixer hK SmallRule.spRep
    SmallRule.spRep_injective (SmallRule.spBilin K 4) SmallRule.spBilin_nondegenerate
    SmallRule.spBilin_isRefl SmallRule.spRep_isometry hdim8 hEab hEc hzE hz1 hW4 hker hT2 hTiso hTE
    hTW
  obtain ⟨D₁, J₁, hpre₁, hns⟩ := ggB2der_prepair hK hM hperf hZ2 hB hxB hx1 hx3 hxL hkerβ heE he1
    he6 hkere
  have hsmall : LargeEvenSmall J := ggB2der_small hK hψinj hJL hW4 hcompl hψJ
  exact hclause ⟨rfl, D₁, J₁, hpre₁, hns⟩ hsmall

theorem ggConfig_not_B2der {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hA1 : GGB2derSympKnown) (hcfg : GGConfig 3 B Bs x L D J)
    (hJ : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) : False := by
  have hBL : B ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_largeEvenStandardType hcfg.1.2.2.2.2.2.2.2
  refine ggConfig_not_B2der_of_model hcfg hJ hBL ?_
  obtain ⟨K, _, _, _, r, _, hK, hr3, ψ, β, hM⟩ := ggB2der_model hA1 hcfg hJ hBL
  exact ⟨K, inferInstance, inferInstance, inferInstance, r, inferInstance, hK, hr3, ψ, β, hM,
    fun y hyD hyx => ggB2der_J_data hA1 hcfg hJ hBL hK hr3 hM hyD hyx⟩

end CFSG.StandardType

module

public import CFSG.RankThree.GF2n.Parrott.Section3RemarksU
import CFSG.RankThree.GF2n.Parrott.Section3RemarksE9
import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks
import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
import CFSG.LocalAnalysis.RankThreeUC.WeakClosure.WeakClosureSetting
import CFSG.LocalAnalysis.RankThreeUC.WeakModules

public section

namespace CFSG.RankThree.GF2n.Parrott.Remarks

open CFSG CFSG.Open CFSG.RankThree.GF2n.Parrott
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (fixedSpace commSpace)

variable {G : Type} [Group G] [Finite G] {z : G}

section Model

set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : ↥QA45.originalSubgroup)

end Model

theorem commutator_J_H_eq_J_of (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z) {σ₁ σ₂ : ↥(H z)}
    (h3₂ : orderOf σ₂ = 3) (hc : Commute σ₁ σ₂) (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G))
    {y u : ↥(H z)} (hy : orderOf y = 9) (hyσ : y ^ 3 = σ₁) (hu : u * σ₁ * u⁻¹ = σ₂) :
    ⁅J z, H z⁆ = J z := by
  let _ : CommGroup (QuotientV.V z) := commGroupV hcomm
  let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp J_le_normalizer_A)
    fun g hg => ?_
  have h3₁ : orderOf σ₁ = 3 := by
    rw [← hyσ, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) (by rw [hy]; norm_num), hy]
  have h8₁ : Nat.card (CJ z (σ₁ : G)) = 8 := card_CJ_eq_eight_of_cube hJ hcard hcomm hCHJ hy hyσ
  have h8₂ : Nat.card (CJ z (σ₂ : G)) = 8 := by
    rw [← hu, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, card_CJ_conj_eq, h8₁]
  have hCJ : CJ z (σ₂ : G) ⊓ CJ z (σ₁ : G) = Subgroup.zpowers z := by
    rw [inf_comm]
    exact CJ_inf_CJ_eq_zpowers hJ hcomm h3₂ hc h8₁ h8₂ hne
  have hfs : ∀ x : ↥(H z), fixedSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers x) =
      fixSubmodule hcomm hJ x := fun x => invariants_zpowers_eq_fixSubmodule hcomm hJ x
  have e := finrank_fixedSpace_eq_add (conjVRepresentation hcomm hJ) h3₂ σ₁ hc.symm
  rw [hfs σ₂, hfs σ₁, fixSubmodule_inf_eq_bot hJ hcomm h3₂ h3₁ hCJ, finrank_bot, zero_add] at e
  have hle : fixSubmodule hcomm hJ σ₁ ≤
      commSpace (conjVRepresentation hcomm hJ) (Subgroup.zpowers σ₂) :=
    inf_eq_right.mp (Submodule.eq_of_le_of_finrank_eq inf_le_right e.symm)
  have htop := (isCompl_fixedSpace_commSpace (conjVRepresentation hcomm hJ) h3₁).sup_eq_top
  rw [hfs σ₁] at htop
  let S : @Submodule (ZMod 2) (Additive (QuotientV.V z)) _ _ (moduleV hcomm hJ) :=
    AddSubgroup.toZModSubmodule 2
      (Subgroup.toAddSubgroup ((⁅J z, H z⁆.subgroupOf (J z)).map (QuotientV.pi z)))
  have hSmem : ∀ v : Additive (QuotientV.V z), v ∈ S ↔
      ∃ k ∈ ⁅J z, H z⁆.subgroupOf (J z), QuotientV.pi z k = Additive.toMul v := by
    intro v
    show v ∈ AddSubgroup.toZModSubmodule 2 _ ↔ _
    rw [AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup, Subgroup.mem_map]
  have hS : ∀ X : Subgroup ↥(H z), commSpace (conjVRepresentation hcomm hJ) X ≤ S := by
    intro X
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, -, v, rfl⟩
    obtain ⟨j, hj⟩ := QuotientV.pi_surjective z (Additive.toMul v)
    rw [SetLike.mem_coe, hSmem]
    refine ⟨conjJ' z x j * j⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, conjJ'_apply_coe, Subgroup.coe_inv,
        Subgroup.commutator_comm, ← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator x.2 j.2
    · change _ = Additive.toMul (conjVLinearMap hcomm hJ x v) / Additive.toMul v
      rw [conjVLinearMap_apply, toMul_ofMul, map_mul, map_inv, ← conjVA_mk, hj, div_eq_mul_inv]
  have hStop : S = ⊤ :=
    eq_top_iff.mpr (htop.symm.le.trans (sup_le (hle.trans (hS _)) (hS _)))
  obtain ⟨k, hk, hkg⟩ := (hSmem _).mp
    (eq_top_iff.mp hStop (Submodule.mem_top (x := Additive.ofMul (QuotientV.pi z ⟨g, hg⟩))))
  have hker : k⁻¹ * ⟨g, hg⟩ ∈ (QuotientV.pi z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, toMul_ofMul, inv_mul_cancel]
  rw [QuotientV.pi_ker, Subgroup.mem_subgroupOf, centerIn_J_eq_zpowers hJ hcomm, ← hcomm] at hker
  have hJJ : ⁅J z, J z⁆ ≤ ⁅J z, H z⁆ := Subgroup.commutator_mono le_rfl J_le_H
  have hmem := mul_mem (Subgroup.mem_subgroupOf.mp hk) (hJJ hker)
  rwa [← Subgroup.coe_mul, mul_inv_cancel_left] at hmem

end CFSG.RankThree.GF2n.Parrott.Remarks

module

public import CFSG.Quasithin.Vol2.GoldschmidtE217Torus
public import CFSG.Quasithin.H13.QRCPairedSection
public import CFSG.Quasithin.Vol2.Ch3E213MShare

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 E2 Ch3E213M
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL projUnitriangular
  projUpperTriangular)
open CFSG.QuasithinUnique.Setup (oddResidualPreimage)
open CFSG.Quasithin.H13.QRC (BenderData benderData_sl2 projSLEquiv sl2_normalizer_upperUnipotent
  map_projSLEquiv_symm_projUnitriangular map_projSLEquiv_symm_projUpperTriangular)
open CFSG.GorensteinWalter (sl2Borel sl2UpperUnipotentSubgroup)
open scoped MatrixGroups

namespace E217R1

theorem benderData_proj {A : Type*} [Group A] [Finite A] {K : Subgroup A} {k : Type} [Field k]
    [Finite k] {n : ℕ} (hk : Nat.card k = 2 ^ n) (θ : K ≃* projectiveSL 2 k) :
    BenderData K ((projUnitriangular 2 k).map θ.symm.toMonoidHom) n ∧
      Subgroup.normalizer (((projUnitriangular 2 k).map θ.symm.toMonoidHom : Subgroup K) :
        Set K) = (projUpperTriangular 2 k).map θ.symm.toMonoidHom := by
  have : CharP k 2 := CFSG.ShultStronglyClosedTI.LinearModel.charP_two_of_card hk
  set e : K ≃* SL(2, k) := θ.trans (projSLEquiv (k := k)).symm with he
  have h1 : (sl2UpperUnipotentSubgroup k).map (projSLEquiv (k := k)).toMonoidHom =
      projUnitriangular 2 k := by
    rw [← map_projSLEquiv_symm_projUnitriangular, Subgroup.map_map]
    convert Subgroup.map_id (projUnitriangular 2 k)
    ext g
    simp
  have h2 : (sl2Borel k).map (projSLEquiv (k := k)).toMonoidHom = projUpperTriangular 2 k := by
    rw [← map_projSLEquiv_symm_projUpperTriangular, Subgroup.map_map]
    convert Subgroup.map_id (projUpperTriangular 2 k)
    ext g
    simp
  have hU : (sl2UpperUnipotentSubgroup k).map e.symm.toMonoidHom =
      (projUnitriangular 2 k).map θ.symm.toMonoidHom := by
    rw [show e.symm.toMonoidHom = θ.symm.toMonoidHom.comp (projSLEquiv (k := k)).toMonoidHom
      from rfl, ← Subgroup.map_map, h1]
  have hB : (sl2Borel k).map e.symm.toMonoidHom =
      (projUpperTriangular 2 k).map θ.symm.toMonoidHom := by
    rw [show e.symm.toMonoidHom = θ.symm.toMonoidHom.comp (projSLEquiv (k := k)).toMonoidHom
      from rfl, ← Subgroup.map_map, h2]
  refine ⟨hU ▸ (benderData_sl2 hk).map e.symm, ?_⟩
  rw [← hU, ← Subgroup.map_equiv_normalizer_eq, sl2_normalizer_upperUnipotent, hB]

variable {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}

theorem false_of_pairedL2
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) (hS : Setting H T M V K)
    (h1 : Case1 H T M K) {n : ℕ} (hn : 2 ≤ n) (hPSL : IsPSL 2 2 n ↥(E2.star M H K))
    (hres : twoResidual M ≤ Subgroup.centralizer (V : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := hS.hyp.minParabolic
  have hVH : V ≤ H := hS.hyp.le_H
  obtain ⟨T', hT', hcharH, hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM', -⟩ :=
    qrcHyp_of_hyp28 hS.hyp hS.charTwo
  have := hel
  have hVQ' : 4 ≤ (V.subgroupOf H ⊓ CFSG.pCore 2 H).relIndex (V.subgroupOf H) := by
    rw [relIndex_subgroupOf_inf_pCore hVH]
    exact hS.four_le
  obtain ⟨k, _, _, hk, ⟨θ⟩⟩ := exists_equiv_projectiveSL_of_isPSL hPSL
  obtain ⟨K₁, K₂, hK, hc, hd, ⟨φ₁⟩, ⟨φ₂⟩⟩ := exists_paired_of_case1 h38 hS h1
  have hQRC :=
    H13.QRC.qrc_paired_even_linear_sections_produce_original_pair_with_full_second_projection_core
      hS.not_solvable hcharH T' hTn hTM' hMH' hmax' hVT' hTV' hVM' hVQ' hk hn hK hc hd
      ⟨φ₁.trans θ⟩ ⟨φ₂.trans θ⟩
  obtain ⟨-, R, θ₁, θ₂, -, -, -, -, -, -, hBeq, hEU, -⟩ := hQRC
  obtain ⟨-, -, -, -, -, -, -, -, hEcard, -⟩ :=
    H13.QRC.bender_section_setup hS.not_solvable T' hTn hTM' hMH' hmax' hVT' hVM'
  set π := QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤) with hπ
  set E := (V.subgroupOf H).map π with hE
  have hcent : ∀ b ∈ (M.subgroupOf H).map π, Odd (orderOf b) → ∀ e ∈ E, b * e = e * b :=
    fun b hb hodd e he => commute_of_odd_of_twoResidual hres π hb hodd he
  have hE₂ : E ≤ ((projUnitriangular 2 k).map θ₂.symm.toMonoidHom).map K₂.subtype :=
    le_of_paired_torus (benderData_proj hk θ₁).1 hn hc (Subgroup.map_subtype_le _) hEU
      (by
        rw [(benderData_proj hk θ₁).2, hBeq]
        exact le_sup_left.trans le_sup_left) hcent
  have hE₁ : E ≤ ((projUnitriangular 2 k).map θ₁.symm.toMonoidHom).map K₁.subtype :=
    le_of_paired_torus (benderData_proj hk θ₂).1 hn (fun a ha b hb => (hc b hb a ha).symm)
      (Subgroup.map_subtype_le _) (by rwa [sup_comm] at hEU)
      (by
        rw [(benderData_proj hk θ₂).2, hBeq]
        exact le_sup_right.trans le_sup_left) hcent
  have hEb : E ≤ ⊥ := by
    rw [← hd]
    exact le_inf (hE₁.trans (Subgroup.map_subtype_le _)) (hE₂.trans (Subgroup.map_subtype_le _))
  have hcard1 : Nat.card E ≤ 1 := by
    have := Subgroup.card_le_of_le hEb
    rwa [Subgroup.card_bot] at this
  have hVQ'' : 4 ≤ Nat.card E := hEcard ▸ hVQ'
  omega


end E217R1

end CFSG.Quasithin

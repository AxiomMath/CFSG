module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_8.Orbit

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped IsMulCommutative commutatorElement

namespace CFSG.Section9

universe u v w

public theorem theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      MF ⊔ C ≤ ambientDerivedSubgroup M := by
  intro hcase
  rcases hcase with
    ⟨h92, _hH0MF, hC, _hpprime, _hqprime, _hpData, _hcomponent, _hrest⟩
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
      _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  have hMFD : MF ≤ ambientDerivedSubgroup M :=
    MF_le_ambientDerived_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  have hCD : C ≤ ambientDerivedSubgroup M := hC.1.trans hUleD
  exact sup_le hMFD hCD

public theorem theorem_9_8_HC_subgroupOf_ambientDerived_relIndex_eq_u_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        ((MF ⊔ C).subgroupOf M).relIndex
          ((ambientDerivedSubgroup M).subgroupOf M) = u := by
  classical
  intro hcase hBarU
  let D : Subgroup G := ambientDerivedSubgroup M
  let HC : Subgroup G := MF ⊔ C
  change (HC.subgroupOf M).relIndex (D.subgroupOf M) = u
  have hidxHC :
      Subgroup.index (HC.subgroupOf M) = q * u :=
    HC_index_eq_q_mul_u_of_hypothesis_9_2_sec9 M MF U W1 W2 C q u
      (case_9_7_a_hypothesis_9_2_sec9 hcase) hBarU
  have hDindex_eq_q : (D.subgroupOf M).index = q :=
    ambientDerived_subgroupOf_index_eq_q_of_hypothesis_9_2_sec9
      M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
  have hHC_le_D : HC ≤ D := by
    dsimp [HC, D]
    exact theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase
  have hHCsub_le_Dsub : HC.subgroupOf M ≤ D.subgroupOf M := by
    intro x hx
    have hxHC : ((x : M) : G) ∈ HC := by
      simpa [HC, Subgroup.mem_subgroupOf] using hx
    have hxD : ((x : M) : G) ∈ D := hHC_le_D hxHC
    simpa [D, Subgroup.mem_subgroupOf] using hxD
  have hright :
      (HC.subgroupOf M).relIndex (D.subgroupOf M) * q = u * q := by
    calc
      (HC.subgroupOf M).relIndex (D.subgroupOf M) * q
          = (HC.subgroupOf M).relIndex (D.subgroupOf M) *
              (D.subgroupOf M).index := by rw [hDindex_eq_q]
      _ = Subgroup.index (HC.subgroupOf M) := by
            exact Subgroup.relIndex_mul_index hHCsub_le_Dsub
      _ = q * u := hidxHC
      _ = u * q := Nat.mul_comm q u
  exact Nat.mul_right_cancel (case_9_7_a_q_prime_sec9 hcase).pos hright

public theorem theorem_9_8_MF_normal_HC_of_case_a_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (MF.subgroupOf (MF ⊔ C)).Normal := by
  intro hcase
  have hHC_le_M :
      MF ⊔ C ≤ M :=
    (theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase).trans
      (section12_ambientDerivedSubgroup_le (E := M))
  rcases case_9_7_a_hypothesis_9_2_sec9 hcase with h92
  rcases h92.mf.1 with ⟨hMFleM, hMFnormalM, _hMFnil, _hMFhall⟩
  have hM_le_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormalM
  have hHC_le_norm_MF : MF ⊔ C ≤ Subgroup.normalizer (MF : Set G) :=
    hHC_le_M.trans hM_le_norm_MF
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (show MF ≤ MF ⊔ C from le_sup_left)).2 hHC_le_norm_MF


public theorem theorem_9_8_H0C_normal_HC_of_case_a_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal := by
  intro hcase
  have hH0C_le_HC : H0 ⊔ C ≤ MF ⊔ C :=
    sup_le_sup (case_9_7_a_H0_le_MF_sec9 hcase) le_rfl
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer hH0C_le_HC).2
  have hH0_le_M : H0 ≤ M :=
    (case_9_7_a_H0_le_MF_sec9 hcase).trans (case_9_7_a_MF_le_M_sec9 hcase)
  have hH0normalM : (H0.subgroupOf M).Normal :=
    case_9_7_a_H0_normal_M_sec9 hcase
  have hM_le_norm_H0 : M ≤ Subgroup.normalizer (H0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_M).1 hH0normalM
  have hMF_norm_H0C :
      MF ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) := by
    apply le_normalizer_sup_of_le_normalizer_left_commutator_right_sec9
    · exact (case_9_7_a_MF_le_M_sec9 hcase).trans hM_le_norm_H0
    · intro n hnMF b hbC
      exact ((case_9_7_a_quotientCentralizerIn_sec9 hcase).2 b
        ((case_9_7_a_quotientCentralizerIn_sec9 hcase).1 hbC)).mp hbC n hnMF
  have hC_norm_H0C :
      C ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) :=
    le_sup_right.trans (Subgroup.le_normalizer (H := H0 ⊔ C))
  exact sup_le hMF_norm_H0C hC_norm_H0C

public theorem theorem_9_8_HC_normal_ambientDerived_subgroupOf_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        (((MF ⊔ C).subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal := by
  intro hcase hBarU
  let D : Subgroup G := ambientDerivedSubgroup M
  let HC : Subgroup G := MF ⊔ C
  rcases hBarU with ⟨hC_le_U_card, hCnormalU, _hcardU⟩
  have h92 := case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.mf.1 with ⟨hMFleM, hMFnormalM, _hMFnil, _hMFhall⟩
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, hD_eq, _hMFUdisj⟩
  have hHC_le_D : HC ≤ D := by
    dsimp [HC, D]
    exact sup_le hMFleD (hC_le_U_card.trans hUleD)
  have hDleM : D ≤ M := by
    dsimp [D]
    exact section12_ambientDerivedSubgroup_le (E := M)
  have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormalM
  have hD_norm_MF : D ≤ Subgroup.normalizer (MF : Set G) :=
    hDleM.trans hM_norm_MF
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
    hUleD.trans hD_norm_MF
  have hU_norm_C : U ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_U_card).1 hCnormalU
  have hU_norm_HC : U ≤ Subgroup.normalizer (HC : Set G) := by
    dsimp [HC]
    exact le_normalizer_sup_of_le_normalizer_sec9 MF C U hU_norm_MF hU_norm_C
  have hMF_norm_HC : MF ≤ Subgroup.normalizer (HC : Set G) :=
    (le_sup_left : MF ≤ HC).trans (Subgroup.le_normalizer (H := HC))
  have hMFU_norm_HC : MF ⊔ U ≤ Subgroup.normalizer (HC : Set G) :=
    sup_le hMF_norm_HC hU_norm_HC
  have hD_norm_HC : D ≤ Subgroup.normalizer (HC : Set G) := by
    simpa [D, hD_eq] using hMFU_norm_HC
  change ((HC.subgroupOf M).subgroupOf (D.subgroupOf M)).Normal
  exact subgroupOf_subgroupOf_normal_of_le_normalizer_sec9 hHC_le_D hD_norm_HC

public theorem theorem_9_8_H0C_normal_M_of_case_a_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      ((H0 ⊔ C).subgroupOf M).Normal := by
  intro hcase
  have hpData :
      ∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
            quotientChiefFactorData_9_6 M MF H0 W1 hp := by
    rcases hcase with
      ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, hpData, _hrest⟩
    exact hpData
  exact theorem_9_H0C_normal_M_source_core_sec9 M MF U W1 W2 H0 C p q
    (case_9_7_a_hypothesis_9_2_sec9 hcase)
    (case_9_7_a_H0_le_MF_sec9 hcase)
    (case_9_7_a_quotientCentralizerIn_sec9 hcase)
    (case_9_7_a_p_prime_sec9 hcase)
    hpData

public theorem theorem_9_8_H0C_normal_ambientDerived_subgroupOf_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (((H0 ⊔ C).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)).Normal := by
  intro hcase
  have hH0CnormalM : ((H0 ⊔ C).subgroupOf M).Normal :=
    theorem_9_8_H0C_normal_M_of_case_a_sec9 M MF U W1 W2 H0 C p q a hcase
  letI : ((H0 ⊔ C).subgroupOf M).Normal := hH0CnormalM
  exact Section1.subgroupOf_normal_of_normal ((H0 ⊔ C).subgroupOf M)
    ((ambientDerivedSubgroup M).subgroupOf M)

public theorem theorem_9_8_H0Uprime_normal_ambientDerived_subgroupOf_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Uprime = (_root_.commutator U).map U.subtype →
        (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal := by
  intro hcase hUprimeEq
  let D : Subgroup G := ambientDerivedSubgroup M
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, hD_eq, _hMFUdisj⟩
  have hDleM : D ≤ M := by
    dsimp [D]
    exact section12_ambientDerivedSubgroup_le (E := M)
  have hH0MF : H0 ≤ MF := case_9_7_a_H0_le_MF_sec9 hcase
  have hUprimeU : Uprime ≤ U := by
    rw [hUprimeEq, Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_le_self U
  have hH0Uprime_le_D : H0 ⊔ Uprime ≤ D :=
    sup_le (hH0MF.trans hMFleD) (hUprimeU.trans hUleD)
  have hH0leM : H0 ≤ M := (hH0MF.trans hMFleD).trans hDleM
  have hM_norm_H0 : M ≤ Subgroup.normalizer (H0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH0leM).1
      (case_9_7_a_H0_normal_M_sec9 hcase)
  have hMF_norm_H0 : MF ≤ Subgroup.normalizer (H0 : Set G) :=
    (hMFleD.trans hDleM).trans hM_norm_H0
  have hU_norm_H0 : U ≤ Subgroup.normalizer (H0 : Set G) :=
    (hUleD.trans hDleM).trans hM_norm_H0
  have hcomm_image :
      (_root_.commutator U).map U.subtype ≤ Subgroup.centralizer (MF : Set G) :=
    (Section8.theorem_8_5_b M MF U W1 W2 h92.typePDefinitionData).1
  have hMF_norm_H0Uprime :
      MF ≤ Subgroup.normalizer ((H0 ⊔ Uprime : Subgroup G) : Set G) := by
    apply le_normalizer_sup_of_le_normalizer_left_commutator_right_sec9
    · exact hMF_norm_H0
    · intro n hnMF b hbUprime
      have hbcent : b ∈ Subgroup.centralizer (MF : Set G) := by
        exact hcomm_image (by simpa [hUprimeEq] using hbUprime)
      have hbcomm : n * b = b * n :=
        (Subgroup.mem_centralizer_iff.mp hbcent) n hnMF
      have hcomm_eq : ⁅b, n⁆ = 1 := by
        rw [commutatorElement_def]
        calc
          b * n * b⁻¹ * n⁻¹ = (n * b) * b⁻¹ * n⁻¹ := by rw [← hbcomm]
          _ = 1 := by group
      rw [hcomm_eq]
      exact H0.one_mem
  have hUprime_comm : Uprime = (⁅U, U⁆ : Subgroup G) := by
    rw [hUprimeEq, Subgroup.map_subtype_commutator]
  have hU_norm_Uprime : U ≤ Subgroup.normalizer (Uprime : Set G) := by
    have hU_norm_comm :
        U ≤ Subgroup.normalizer (((⁅U, U⁆ : Subgroup G) : Set G)) :=
      normalizer_le_normalizer_commutator_self_sec9 U U
        (Subgroup.le_normalizer (H := U))
    simpa [hUprime_comm] using hU_norm_comm
  have hU_norm_H0Uprime :
      U ≤ Subgroup.normalizer ((H0 ⊔ Uprime : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer_sec9 H0 Uprime U
      hU_norm_H0 hU_norm_Uprime
  have hMFU_norm_H0Uprime :
      MF ⊔ U ≤ Subgroup.normalizer ((H0 ⊔ Uprime : Subgroup G) : Set G) :=
    sup_le hMF_norm_H0Uprime hU_norm_H0Uprime
  have hD_norm_H0Uprime :
      D ≤ Subgroup.normalizer ((H0 ⊔ Uprime : Subgroup G) : Set G) := by
    simpa [D, hD_eq] using hMFU_norm_H0Uprime
  exact subgroupOf_subgroupOf_normal_of_le_normalizer_sec9
    hH0Uprime_le_D hD_norm_H0Uprime

public theorem theorem_9_8_HC_normal_M_of_case_a_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        ((MF ⊔ C).subgroupOf M).Normal := by
  intro hcase hBarU
  let D : Subgroup G := ambientDerivedSubgroup M
  let HC : Subgroup G := MF ⊔ C
  rcases hBarU with ⟨hC_le_U_card, hCnormalU, _hcardU⟩
  have h92 := case_9_7_a_hypothesis_9_2_sec9 hcase
  have hC : quotientCentralizerIn MF H0 U C :=
    case_9_7_a_quotientCentralizerIn_sec9 hcase
  rcases h92.mf.1 with ⟨hMFleM, hMFnormalM, _hMFnil, _hMFhall⟩
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, hcompMW1, hUleD,
      _hUnil, hW1normUInM, hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
      _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  have hHC_le_M : HC ≤ M := by
    dsimp [HC]
    exact (theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase).trans
      (section12_ambientDerivedSubgroup_le (E := M))
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hHC_le_M).2 ?_
  have hDleM : D ≤ M := by
    dsimp [D]
    exact section12_ambientDerivedSubgroup_le (E := M)
  have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormalM
  have hD_norm_MF : D ≤ Subgroup.normalizer (MF : Set G) :=
    hDleM.trans hM_norm_MF
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
    hUleD.trans hD_norm_MF
  have hU_norm_C : U ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_U_card).1 hCnormalU
  have hU_norm_HC : U ≤ Subgroup.normalizer (HC : Set G) := by
    dsimp [HC]
    exact le_normalizer_sup_of_le_normalizer_sec9 MF C U hU_norm_MF hU_norm_C
  have hMF_norm_HC : MF ≤ Subgroup.normalizer (HC : Set G) :=
    (le_sup_left : MF ≤ HC).trans (Subgroup.le_normalizer (H := HC))
  have hMFU_norm_HC : MF ⊔ U ≤ Subgroup.normalizer (HC : Set G) :=
    sup_le hMF_norm_HC hU_norm_HC
  have hD_norm_HC : D ≤ Subgroup.normalizer (HC : Set G) := by
    have hD_eq : D = MF ⊔ U := by
      dsimp [D]
      exact hcompDU.2.2.1
    simpa [D, hD_eq] using hMFU_norm_HC
  have hW1_le_M : W1 ≤ M := hW1hall.1
  have hW1_norm_U : W1 ≤ Subgroup.normalizer (U : Set G) := by
    intro w hw
    exact (mem_subgroupNormalizerIn.mp (hW1normUInM hw)).1
  have hW1_norm_MF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    hW1_le_M.trans hM_norm_MF
  have hH0_le_M : H0 ≤ M :=
    (case_9_7_a_H0_le_MF_sec9 hcase).trans hMFleM
  have hH0_normal_M : (H0.subgroupOf M).Normal :=
    case_9_7_a_H0_normal_M_sec9 hcase
  have hW1_norm_C : W1 ≤ Subgroup.normalizer (C : Set G) :=
    quotientCentralizerIn_le_normalizer_of_le_normalizers_sec9
      (M := M) (MF := MF) (U := U) (H0 := H0) (N := W1)
      hW1_le_M hW1_norm_U hW1_norm_MF hH0_le_M hH0_normal_M hC
  have hW1_norm_HC : W1 ≤ Subgroup.normalizer (HC : Set G) := by
    dsimp [HC]
    exact le_normalizer_sup_of_le_normalizer_sec9 MF C W1
      hW1_norm_MF hW1_norm_C
  have hDW1_norm_HC : D ⊔ W1 ≤ Subgroup.normalizer (HC : Set G) :=
    sup_le hD_norm_HC hW1_norm_HC
  have hM_eq : M = D ⊔ W1 := by
    dsimp [D]
    exact hcompMW1.2.2.1
  simpa [hM_eq] using hDW1_norm_HC

public theorem theorem_9_8_MF_C_isComplement_HC_of_case_a_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (MF.subgroupOf (MF ⊔ C)).IsComplement' (C.subgroupOf (MF ⊔ C)) := by
  intro hcase
  have hMFnormalHC : (MF.subgroupOf (MF ⊔ C)).Normal :=
    theorem_9_8_MF_normal_HC_of_case_a_sec9 M MF U W1 W2 H0 C p q a hcase
  have hC_le_U : C ≤ U :=
    (case_9_7_a_quotientCentralizerIn_sec9 hcase).1
  have h92 := case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', _hUleD, _hD_eq, hMFUdisj⟩
  have hdisjMFC : Disjoint MF C := by
    rw [disjoint_iff] at hMFUdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : x ∈ MF ⊓ U := ⟨hx.1, hC_le_U hx.2⟩
      simpa [hMFUdisj] using hxAmb
    · exact bot_le
  have hdisjMFC_sub :
      Disjoint (MF.subgroupOf (MF ⊔ C)) (C.subgroupOf (MF ⊔ C)) := by
    rw [disjoint_iff] at hdisjMFC ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ MF ⊓ C := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf] using hx.1,
          by simpa [Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hdisjMFC] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hMF_C_supTop : MF.subgroupOf (MF ⊔ C) ⊔ C.subgroupOf (MF ⊔ C) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := MF) (A' := C) (B := MF ⊔ C)
      le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_eq_top.2 le_rfl
  letI : (MF.subgroupOf (MF ⊔ C)).Normal := hMFnormalHC
  exact isComplement'_of_disjoint_sup_eq_top_of_normal
    (MF.subgroupOf (MF ⊔ C)) (C.subgroupOf (MF ⊔ C))
    hdisjMFC_sub hMF_C_supTop

public theorem subgroupOfClassFunction_injective_sec9
    {G : Type u} [Group G] {H T : Subgroup G} (hHT : H ≤ T) :
    Function.Injective
      (fun θ : Section1.ClassFunction H =>
        Section1.subgroupOfClassFunction (T := T) θ) := by
  intro θ ψ hθψ
  ext h
  have hval := congrFun hθψ ((Subgroup.subgroupOfEquivOfLe hHT).symm h)
  simpa [Section1.subgroupOfClassFunction, Subgroup.subgroupOfEquivOfLe] using hval

public theorem degree_eq_one_of_irreducible_subgroupInKernel_commutator_sec9
    {G : Type u} [Group G] [Finite G]
    {θ : Section1.ClassFunction G}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hker : Section1.subgroupInKernel' θ (_root_.commutator G)) :
    Section1.degree θ = (1 : ℂ) := by
  classical
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  have hθkerρ : Section1.subgroupInKernel' ρ.character (_root_.commutator G) := by
    simpa [hθeq] using hker
  have hkerRep : Section1.subgroupInRepresentationKernel ρ (_root_.commutator G) :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ
      (_root_.commutator G)).mp hθkerρ
  let ρq : Representation ℂ (G ⧸ _root_.commutator G) (Fin n → ℂ) :=
    Section1.quotientRepresentationOfKernelSubgroup ρ (_root_.commutator G) hkerRep
  let q : G →* G ⧸ _root_.commutator G := QuotientGroup.mk' (_root_.commutator G)
  have hcomp_eq : ρq.comp q = ρ := by
    apply MonoidHom.ext
    intro g
    exact Section1.quotientRepresentationOfKernelSubgroup_mk ρ
      (_root_.commutator G) hkerRep g
  have hρqirr : Representation.IsIrreducible ρq := by
    apply Section6.representation_isIrreducible_of_comp_surjective ρq q
      (QuotientGroup.mk'_surjective (_root_.commutator G))
    simpa [hcomp_eq] using hρirr
  haveI : IsMulCommutative (G ⧸ _root_.commutator G) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (by
      intro x hx
      exact hx)
  have hn : n = 1 := by
    haveI : Representation.IsIrreducible ρq := hρqirr
    simpa using
      (Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (ρ := ρq))
  rw [hθeq, Section1.degree_representation_character]
  simp [hn]

public theorem monoidHom_mem_commutator_of_mem_sec9
    {G H : Type u} [Group G] [Group H] (f : G →* H) {x : G}
    (hx : x ∈ _root_.commutator G) :
    f x ∈ _root_.commutator H := by
  rw [commutator_eq_closure] at hx ⊢
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨a, b, rfl⟩
    exact Subgroup.subset_closure
      ⟨f a, f b, by rw [map_commutatorElement]⟩
  · rw [map_one]
    exact (Subgroup.closure (commutatorSet H)).one_mem
  · intro a b _ha_mem _hb_mem ha hb
    simpa [map_mul] using (Subgroup.closure (commutatorSet H)).mul_mem ha hb
  · intro a _ha_mem ha
    simpa [map_inv] using (Subgroup.closure (commutatorSet H)).inv_mem ha

public theorem commutator_le_subgroupOf_of_isComplement'_pairwise_sec9
    {G : Type u} [Group G]
    {K A B N : Subgroup G}
    (_hAK : A ≤ K) (_hBK : B ≤ K) (_hNK : N ≤ K)
    [hNnormalK : (N.subgroupOf K).Normal]
    (hcomp : (A.subgroupOf K).IsComplement' (B.subgroupOf K))
    (hAA : ⁅A, A⁆ ≤ N) (hAB : ⁅A, B⁆ ≤ N) (hBB : ⁅B, B⁆ ≤ N) :
    _root_.commutator K ≤ N.subgroupOf K := by
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
  let qK : K →* K ⧸ N.subgroupOf K := QuotientGroup.mk' (N.subgroupOf K)
  have hcomm_AB : ∀ (u v : K), (u : G) ∈ A → (v : G) ∈ B →
      qK u * qK v = qK v * qK u := by
    intro u v huA hvB
    rw [← commutatorElement_eq_one_iff_mul_comm]
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := N.subgroupOf K) ⁅u, v⁆).mpr (by
      rw [Subgroup.mem_subgroupOf]
      exact hAB (Subgroup.commutator_mem_commutator huA hvB))
  have hcomm_AA : ∀ (u v : K), (u : G) ∈ A → (v : G) ∈ A →
      qK u * qK v = qK v * qK u := by
    intro u v huA hvA
    rw [← commutatorElement_eq_one_iff_mul_comm]
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := N.subgroupOf K) ⁅u, v⁆).mpr (by
      rw [Subgroup.mem_subgroupOf]
      exact hAA (Subgroup.commutator_mem_commutator huA hvA))
  have hcomm_BB : ∀ (u v : K), (u : G) ∈ B → (v : G) ∈ B →
      qK u * qK v = qK v * qK u := by
    intro u v huB hvB
    rw [← commutatorElement_eq_one_iff_mul_comm]
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := N.subgroupOf K) ⁅u, v⁆).mpr (by
      rw [Subgroup.mem_subgroupOf]
      exact hBB (Subgroup.commutator_mem_commutator huB hvB))
  refine ⟨?_⟩
  apply Std.Commutative.mk
  intro x
  obtain ⟨x0, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf K) x
  intro y
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf K) y
  rcases hcomp.2 x0 with ⟨⟨a, b⟩, hxab⟩
  rcases hcomp.2 y0 with ⟨⟨c, d⟩, hycd⟩
  have haA : (a : G) ∈ A := a.2
  have hbB : (b : G) ∈ B := b.2
  have hcA : (c : G) ∈ A := c.2
  have hdB : (d : G) ∈ B := d.2
  have hxq : qK x0 = qK a * qK b := by rw [← hxab]; simp [qK]
  have hyq : qK y0 = qK c * qK d := by rw [← hycd]; simp [qK]
  have hAC := hcomm_AA a c haA hcA
  have hAD := hcomm_AB a d haA hdB
  have hCB := hcomm_AB c b hcA hbB
  have hBC : qK b * qK c = qK c * qK b := hCB.symm
  have hBD := hcomm_BB b d hbB hdB
  calc
    qK x0 * qK y0 = (qK a * qK b) * (qK c * qK d) := by rw [hxq, hyq]
    _ = qK a * (qK b * qK c) * qK d := by simp [mul_assoc]
    _ = qK a * (qK c * qK b) * qK d := by rw [hBC]
    _ = (qK a * qK c) * (qK b * qK d) := by simp [mul_assoc]
    _ = (qK c * qK a) * (qK d * qK b) := by rw [hAC, hBD]
    _ = qK c * (qK a * qK d) * qK b := by simp [mul_assoc]
    _ = qK c * (qK d * qK a) * qK b := by rw [hAD]
    _ = (qK c * qK d) * (qK a * qK b) := by simp [mul_assoc]
    _ = qK y0 * qK x0 := by rw [hxq, hyq]


public theorem theorem_9_8_H0Cprime_le_HC_of_case_a_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Cprime = (_root_.commutator C).map C.subtype →
        H0 ⊔ Cprime ≤ MF ⊔ C := by
  intro hcase hCprimeEq
  have hH0MF : H0 ≤ MF := case_9_7_a_H0_le_MF_sec9 hcase
  have hCprimeC : Cprime ≤ C := by
    rw [hCprimeEq]
    rintro x ⟨y, _hy, rfl⟩
    exact y.property
  exact sup_le_sup hH0MF hCprimeC

public theorem theorem_9_8_H0Cprime_normal_HC_of_case_a_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Cprime = (_root_.commutator C).map C.subtype →
        ((H0 ⊔ Cprime).subgroupOf (MF ⊔ C)).Normal := by
  intro hcase hCprimeEq
  have hN_le_HC : H0 ⊔ Cprime ≤ MF ⊔ C :=
    theorem_9_8_H0Cprime_le_HC_of_case_a_sec9
      M MF U W1 W2 H0 C Cprime p q a hcase hCprimeEq
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer hN_le_HC).2
  let N : Subgroup G := H0 ⊔ Cprime
  have hCprimeC : Cprime ≤ C := by
    rw [hCprimeEq]
    rintro x ⟨y, _hy, rfl⟩
    exact y.property
  have hCprime_comm : Cprime = (⁅C, C⁆ : Subgroup G) := by
    rw [hCprimeEq, Subgroup.map_subtype_commutator]
  have h92 := case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
  have hDleM : ambientDerivedSubgroup M ≤ M :=
    section12_ambientDerivedSubgroup_le (E := M)
  have hH0_le_M : H0 ≤ M :=
    (case_9_7_a_H0_le_MF_sec9 hcase).trans
      (case_9_7_a_MF_le_M_sec9 hcase)
  have hM_norm_H0 : M ≤ Subgroup.normalizer (H0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_M).1
      (case_9_7_a_H0_normal_M_sec9 hcase)
  have hMF_norm_H0 : MF ≤ Subgroup.normalizer (H0 : Set G) :=
    (case_9_7_a_MF_le_M_sec9 hcase).trans hM_norm_H0
  have hC_le_U : C ≤ U := (case_9_7_a_quotientCentralizerIn_sec9 hcase).1
  have hC_norm_H0 : C ≤ Subgroup.normalizer (H0 : Set G) :=
    hC_le_U.trans (hUleD.trans (hDleM.trans hM_norm_H0))
  have hMF_norm_N : MF ≤ Subgroup.normalizer (N : Set G) := by
    dsimp [N]
    apply le_normalizer_sup_of_le_normalizer_left_commutator_right_sec9
    · exact hMF_norm_H0
    · intro n hnMF b hbCprime
      have hbC : b ∈ C := hCprimeC hbCprime
      have hbU : b ∈ U := hC_le_U hbC
      exact ((case_9_7_a_quotientCentralizerIn_sec9 hcase).2 b hbU).mp
        hbC n hnMF
  have hC_norm_Cprime : C ≤ Subgroup.normalizer (Cprime : Set G) := by
    have hC_norm_comm :
        C ≤ Subgroup.normalizer (((⁅C, C⁆ : Subgroup G) : Set G)) :=
      normalizer_le_normalizer_commutator_self_sec9 C C
        (Subgroup.le_normalizer (H := C))
    simpa [hCprime_comm] using hC_norm_comm
  have hC_norm_N : C ≤ Subgroup.normalizer (N : Set G) := by
    dsimp [N]
    exact le_normalizer_sup_of_le_normalizer_sec9 H0 Cprime C
      hC_norm_H0 hC_norm_Cprime
  exact sup_le hMF_norm_N hC_norm_N

public theorem theorem_9_8_HC_commutator_le_H0Cprime_subgroupOf_case_a_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Cprime = (_root_.commutator C).map C.subtype →
        _root_.commutator
            (((MF ⊔ C).subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M)) ≤
          ((((H0 ⊔ Cprime).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
              (((MF ⊔ C).subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M))) := by
  intro hcase hCprimeEq
  let D : Subgroup G := ambientDerivedSubgroup M
  let HC : Subgroup G := MF ⊔ C
  let N : Subgroup G := H0 ⊔ Cprime
  have hN_le_HC : N ≤ HC := by
    dsimp [N, HC]
    exact theorem_9_8_H0Cprime_le_HC_of_case_a_sec9
      M MF U W1 W2 H0 C Cprime p q a hcase hCprimeEq
  have hCprimeC : Cprime ≤ C := by
    rw [hCprimeEq]
    rintro x ⟨y, _hy, rfl⟩
    exact y.property
  have hNnormalHC : (N.subgroupOf HC).Normal := by
    dsimp [N, HC]
    exact theorem_9_8_H0Cprime_normal_HC_of_case_a_sec9
      M MF U W1 W2 H0 C Cprime p q a hcase hCprimeEq
  letI : (N.subgroupOf HC).Normal := hNnormalHC
  have hMFroot_le_H0sub : _root_.commutator MF ≤ H0.subgroupOf MF := by
    rcases case_9_7_a_hoReductionData_sec9 hcase with ⟨hp, _hpval, hpData⟩
    rcases hpData with
      ⟨_hH0MF, _hMFM, _hH0normalM, _hH0normalMF, _hH0ltMF, hElem,
        _hrest⟩
    rcases hElem with ⟨hnormal, hbarElem⟩
    letI : (H0.subgroupOf MF).Normal := hnormal
    letI : IsElementaryAbelian hp.val (MF ⧸ H0.subgroupOf MF) := hbarElem
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    infer_instance
  have hAA : ⁅MF, MF⁆ ≤ N := by
    intro x hx
    have hxmap : x ∈ (_root_.commutator MF).map MF.subtype := by
      simpa [Subgroup.map_subtype_commutator] using hx
    rcases hxmap with ⟨y, hy, hyx⟩
    have hyH0 : (y : G) ∈ H0 := hMFroot_le_H0sub hy
    rw [← hyx]
    exact Subgroup.mem_sup_left hyH0
  have hCMF_le_H0 : ⁅C, MF⁆ ≤ H0 := by
    rw [Subgroup.commutator_le]
    intro c hc m hm
    have hcent := case_9_7_a_quotientCentralizerIn_sec9 hcase
    exact (hcent.2 c (hcent.1 hc)).mp hc m hm
  have hAB : ⁅MF, C⁆ ≤ N := by
    intro x hx
    exact Subgroup.mem_sup_left
      (hCMF_le_H0 ((Subgroup.commutator_comm_le MF C) hx))
  have hBB : ⁅C, C⁆ ≤ N := by
    intro x hx
    exact Subgroup.mem_sup_right (by
      simpa [hCprimeEq, Subgroup.map_subtype_commutator] using hx)
  have hrootHC : _root_.commutator HC ≤ N.subgroupOf HC := by
    exact commutator_le_subgroupOf_of_isComplement'_pairwise_sec9
      (K := HC) (A := MF) (B := C) (N := N)
      le_sup_left le_sup_right hN_le_HC
      (theorem_9_8_MF_C_isComplement_HC_of_case_a_sec9
        M MF U W1 W2 H0 C p q a hcase)
      hAA hAB hBB
  let Dm : Subgroup M := D.subgroupOf M
  let K : Subgroup Dm := (HC.subgroupOf M).subgroupOf Dm
  change _root_.commutator K ≤
    (((N.subgroupOf M).subgroupOf Dm).subgroupOf K)
  intro x hx
  let φ : K →* HC :=
    { toFun := fun x =>
        ⟨(((x : Dm) : M) : G), by
          have hxHCm : ((x : Dm) : M) ∈ HC.subgroupOf M := by
            have hxK : (x : Dm) ∈ (HC.subgroupOf M).subgroupOf Dm := by
              exact x.property
            change ((x : Dm) : M) ∈ HC.subgroupOf M at hxK
            exact hxK
          simpa [Subgroup.mem_subgroupOf] using hxHCm⟩
      map_one' := by
        ext
        rfl
      map_mul' := by
        intro a b
        ext
        rfl }
  have hxHC : φ x ∈ _root_.commutator HC :=
    monoidHom_mem_commutator_of_mem_sec9 φ hx
  have hxNsub : φ x ∈ N.subgroupOf HC := hrootHC hxHC
  have hxN : ((φ x : HC) : G) ∈ N := by
    simpa [Subgroup.mem_subgroupOf] using hxNsub
  rw [Subgroup.mem_subgroupOf]
  change (((x : Dm) : M) : G) ∈ N
  simpa [φ] using hxN

public theorem irreducible_degree_nat_le_induced_linear_index_of_inner_sec9
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {θ : Section1.ClassFunction L} {ψ : Section1.ClassFunction K}
    {d : ℕ} :
    Section1.IsIrreducibleCharacterOnGroup θ →
      Section1.IsIrreducibleCharacterOnGroup ψ →
        Section1.degree ψ = (1 : ℂ) →
          Section1.scalarProduct K ψ (Section1.subgroupRestriction K θ) ≠ 0 →
            Section1.degree θ = (d : ℂ) →
              d ≤ Subgroup.index K := by
  classical
  intro hθirr hψirr hψdeg hinner hθdeg
  rcases hθirr with ⟨nθ, ρθ, hρθirr, hθeq⟩
  rcases hψirr with ⟨nψ, ρψ, _hρψirr, hψeq⟩
  let indρψ : Representation ℂ L (Representation.IndV K.subtype ρψ) :=
    Representation.ind K.subtype ρψ
  haveI : FiniteDimensional ℂ (Representation.IndV K.subtype ρψ) :=
    Theory.Representation.finiteDimensional_ind K ρψ
  have hθclass : Section1.IsClassFunction θ := by
    intro x g
    rw [hθeq]
    simpa [mul_assoc] using Representation.char_conj (ρ := ρθ) g x
  have hIndInner :
      Section1.scalarProduct L (Section1.inducedCF K ψ) θ ≠ 0 := by
    rw [Section1.scalarProduct_inducedCF_left K ψ θ hθclass]
    exact hinner
  have hIndInnerRep :
      Section1.scalarProduct L indρψ.character ρθ.character ≠ 0 := by
    simpa [indρψ, hθeq, hψeq,
      Section1.inducedCF_eq_representation_character K ρψ] using hIndInner
  have hfinrank_ne :
      (Module.finrank ℂ (Representation.IntertwiningMap ρθ indρψ) : ℂ) ≠ 0 := by
    simpa [Section1.scalarProduct_representation_char_eq_finrank ρθ indρψ]
      using hIndInnerRep
  have hfinrank_nat_ne :
      Module.finrank ℂ (Representation.IntertwiningMap ρθ indρψ) ≠ 0 := by
    intro hzero
    apply hfinrank_ne
    simp [hzero]
  have hfinrank_pos :
      0 < Module.finrank ℂ (Representation.IntertwiningMap ρθ indρψ) :=
    Nat.pos_of_ne_zero hfinrank_nat_ne
  rw [Module.finrank_pos_iff_exists_ne_zero] at hfinrank_pos
  rcases hfinrank_pos with ⟨f, hf⟩
  have hf_inj : Function.Injective f := by
    letI : Representation.IsIrreducible ρθ := hρθirr
    rcases (Representation.IsIrreducible.injective_or_eq_zero
        (ρ := ρθ) (σ := indρψ) f) with hinj | hzero
    · exact hinj
    · exact (hf hzero).elim
  have hnθ_le_ind :
      nθ ≤ Module.finrank ℂ (Representation.IndV K.subtype ρψ) := by
    simpa [Module.finrank_fin_fun] using
      (LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) hf_inj)
  have hfinrank_ind_eq_index :
      Module.finrank ℂ (Representation.IndV K.subtype ρψ) = Subgroup.index K := by
    have hdeg_ind :
        Section1.degree (Section1.inducedCF K ψ) = (Subgroup.index K : ℂ) := by
      rw [Section1.degree_inducedClassFunction, hψdeg]
      simp
    have hdeg_ind_rep :
        Section1.degree (Section1.inducedCF K ψ) =
          (Module.finrank ℂ (Representation.IndV K.subtype ρψ) : ℂ) := by
      rw [hψeq, Section1.inducedCF_eq_representation_character K ρψ,
        Section1.degree_representation_character]
    have hcast :
        (Module.finrank ℂ (Representation.IndV K.subtype ρψ) : ℂ) =
          (Subgroup.index K : ℂ) :=
      hdeg_ind_rep.symm.trans hdeg_ind
    exact_mod_cast hcast
  have hnθ_eq_d : nθ = d := by
    have hcast : (nθ : ℂ) = (d : ℂ) := by
      simpa [hθeq, Section1.degree_representation_character,
        Module.finrank_fin_fun] using hθdeg
    exact_mod_cast hcast
  simpa [hnθ_eq_d, hfinrank_ind_eq_index] using hnθ_le_ind


public theorem theorem_9_8_case_a_underlying_constituent_degree_le_barU_of_H0Cprime_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (p q a u dθ : ℕ)
    (θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Cprime = (_root_.commutator C).map C.subtype →
          Section1.IsIrreducibleCharacterOnGroup θ →
            ¬ Section1.subgroupInKernel' θ
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
            Section1.subgroupInKernel' θ
              (((H0 ⊔ Cprime).subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
            Section1.degree θ = (dθ : ℂ) →
              dθ ≤ u := by
  classical
  intro hcase hBarU hCprimeEq hθirr _hθnotMF hθkerH0Cprime hθdeg
  let D : Subgroup G := ambientDerivedSubgroup M
  let Dm : Subgroup M := D.subgroupOf M
  let HC : Subgroup G := MF ⊔ C
  let K : Subgroup Dm := (HC.subgroupOf M).subgroupOf Dm
  let A : Subgroup Dm := ((H0 ⊔ Cprime).subgroupOf M).subgroupOf Dm
  rcases exists_irreducible_constituent_of_subgroupRestriction_sec9 K hθirr with
    ⟨ψ, hψirr, hψinner⟩
  have hψkerA : Section1.subgroupInKernel' ψ (A.subgroupOf K) :=
    subgroupInKernel'_constituent_of_subgroupRestriction_kernel_sec9
      K A hθirr (by simpa [D, Dm, A] using hθkerH0Cprime) hψirr
      (by simpa [D, Dm, HC, K] using hψinner)
  have hcomm_le : _root_.commutator K ≤ A.subgroupOf K := by
    dsimp [K, A, Dm, D, HC]
    exact theorem_9_8_HC_commutator_le_H0Cprime_subgroupOf_case_a_sec9
      M MF U W1 W2 H0 C Cprime p q a hcase hCprimeEq
  have hψkerComm :
      Section1.subgroupInKernel' ψ (_root_.commutator K) := by
    intro x
    exact hψkerA ⟨x.1, hcomm_le x.2⟩
  have hψdeg : Section1.degree ψ = (1 : ℂ) :=
    degree_eq_one_of_irreducible_subgroupInKernel_commutator_sec9
      hψirr hψkerComm
  have hdeg_le_index :
      dθ ≤ Subgroup.index K :=
    irreducible_degree_nat_le_induced_linear_index_of_inner_sec9 K
      hθirr hψirr hψdeg (by simpa [D, Dm, HC, K] using hψinner)
      (by simpa [D, Dm] using hθdeg)
  have hidx :
      Subgroup.index K = u := by
    simpa [D, Dm, HC, K, Subgroup.relIndex] using
      theorem_9_8_HC_subgroupOf_ambientDerived_relIndex_eq_u_sec9
        M MF U W1 W2 H0 C p q a u hcase hBarU
  exact hdeg_le_index.trans_eq hidx

@[expose] public noncomputable def quotientInfSupEquiv_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 HC H0C : Subgroup G)
    [(H0.subgroupOf MF).Normal]
    [(H0C.subgroupOf HC).Normal]
    (hMFHC : MF ≤ HC)
    (hH0CinfMF : H0C ⊓ MF = H0)
    (hsup : H0C.subgroupOf HC ⊔ MF.subgroupOf HC = ⊤) :
    (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) := by
  classical
  let φ : MF →* HC ⧸ H0C.subgroupOf HC :=
    (QuotientGroup.mk' (H0C.subgroupOf HC)).comp (Subgroup.inclusion hMFHC)
  have hφker : φ.ker = H0.subgroupOf MF := by
    ext x
    constructor
    · intro hx
      change φ x = 1 at hx
      have hxH0C : (x : G) ∈ H0C := by
        have hxH0Cs :
            Subgroup.inclusion hMFHC x ∈ H0C.subgroupOf HC :=
          (QuotientGroup.eq_one_iff (N := H0C.subgroupOf HC)
            (x := Subgroup.inclusion hMFHC x)).1 hx
        simpa [Subgroup.mem_subgroupOf] using hxH0Cs
      have hxinf : (x : G) ∈ H0C ⊓ MF := ⟨hxH0C, x.property⟩
      have hxH0 : (x : G) ∈ H0 := by
        rw [← hH0CinfMF]
        exact hxinf
      simpa [Subgroup.mem_subgroupOf] using hxH0
    · intro hx
      change φ x = 1
      apply (QuotientGroup.eq_one_iff (N := H0C.subgroupOf HC)
        (x := Subgroup.inclusion hMFHC x)).2
      have hxH0 : (x : G) ∈ H0 := by
        simpa [Subgroup.mem_subgroupOf] using hx
      have hxinf : (x : G) ∈ H0C ⊓ MF := by
        rw [hH0CinfMF]
        exact hxH0
      simpa [Subgroup.mem_subgroupOf] using hxinf.1
  have hφsurj : Function.Surjective φ := by
    intro y
    rcases QuotientGroup.mk'_surjective (H0C.subgroupOf HC) y with ⟨h, rfl⟩
    have hmem : h ∈ H0C.subgroupOf HC ⊔ MF.subgroupOf HC := by
      rw [hsup]
      trivial
    rcases (Subgroup.mem_sup_of_normal_left
        (s := H0C.subgroupOf HC) (t := MF.subgroupOf HC) (x := h)).1 hmem with
      ⟨a, ha, b, hb, hab⟩
    let bMF : MF := ⟨(b : G), by
      simpa [Subgroup.mem_subgroupOf] using hb⟩
    refine ⟨bMF, ?_⟩
    have hqeq :
        QuotientGroup.mk' (H0C.subgroupOf HC) h =
          QuotientGroup.mk' (H0C.subgroupOf HC) b := by
      rw [← hab]
      simp [ha]
    have hb_incl : Subgroup.inclusion hMFHC bMF = b := by
      apply Subtype.ext
      rfl
    change QuotientGroup.mk' (H0C.subgroupOf HC)
        (Subgroup.inclusion hMFHC bMF) =
      QuotientGroup.mk' (H0C.subgroupOf HC) h
    rw [hb_incl]
    exact hqeq.symm
  haveI : φ.ker.Normal := MonoidHom.normal_ker φ
  exact (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)

public theorem theorem_9_8_H0C_subgroupOf_HC_relIndex_eq_p_pow_q_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      ((H0 ⊔ C).subgroupOf M).relIndex ((MF ⊔ C).subgroupOf M) = p ^ q := by
  classical
  intro hcase
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  have hHC_le_M : HC ≤ M := by
    dsimp [HC]
    exact (theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase).trans
      (section12_ambientDerivedSubgroup_le (E := M))
  have hH0CnormalHC : (H0C.subgroupOf HC).Normal := by
    dsimp [H0C, HC]
    exact theorem_9_8_H0C_normal_HC_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase
  have hH0normalMF : (H0.subgroupOf MF).Normal :=
    case_9_7_a_H0_normal_MF_sec9 hcase
  letI : (H0.subgroupOf MF).Normal := hH0normalMF
  letI : (H0C.subgroupOf HC).Normal := hH0CnormalHC
  have hH0CinfMF : H0C ⊓ MF = H0 := by
    dsimp [H0C]
    rcases hcase with ⟨h92, hH0MF, hC, hpprime, _hqprime, hpData, _hrest⟩
    exact theorem_9_H0C_inf_MF_eq_H0_source_core_sec9
      M MF U W1 W2 H0 C p q h92 hH0MF hC hpprime hpData
  have hsup : H0C.subgroupOf HC ⊔ MF.subgroupOf HC = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := H0C) (A' := MF) (B := HC)]
    · apply Subgroup.subgroupOf_eq_top.2
      dsimp [H0C, HC]
      exact sup_le
        (show MF ≤ (H0 ⊔ C) ⊔ MF from le_sup_right)
        (show C ≤ (H0 ⊔ C) ⊔ MF from le_sup_right.trans le_sup_left)
    · dsimp [H0C, HC]
      exact sup_le_sup (case_9_7_a_H0_le_MF_sec9 hcase) le_rfl
    · dsimp [HC]
      exact le_sup_left
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
  have hcard :
      Nat.card (HC ⧸ H0C.subgroupOf HC) =
        Nat.card (MF ⧸ H0.subgroupOf MF) := by
    exact Nat.card_congr e.symm.toEquiv
  rw [Subgroup.relIndex_subgroupOf (H := H0C) (K := HC) (L := M) hHC_le_M]
  change Nat.card (HC ⧸ H0C.subgroupOf HC) = p ^ q
  rw [hcard]
  exact case_9_7_a_quotient_cardinality_sec9 hcase

public theorem theorem_9_8_H0C_subgroupOf_ambientDerived_relIndex_eq_p_pow_q_mul_u_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        ((H0 ⊔ C).subgroupOf M).relIndex
          ((ambientDerivedSubgroup M).subgroupOf M) = p ^ q * u := by
  intro hcase hBarU
  let D : Subgroup G := ambientDerivedSubgroup M
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  have hHC_le_D : HC ≤ D := by
    dsimp [HC, D]
    exact theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase
  have hH0C_le_HC : H0C ≤ HC := by
    dsimp [H0C, HC]
    exact sup_le_sup (case_9_7_a_H0_le_MF_sec9 hcase) le_rfl
  have hH0Cm_le_HCm :
      H0C.subgroupOf M ≤ HC.subgroupOf M := by
    intro x hx
    exact hH0C_le_HC hx
  have hHCm_le_Dm :
      HC.subgroupOf M ≤ D.subgroupOf M := by
    intro x hx
    exact hHC_le_D hx
  have hH0C_HC :
      (H0C.subgroupOf M).relIndex (HC.subgroupOf M) = p ^ q := by
    dsimp [H0C, HC]
    exact theorem_9_8_H0C_subgroupOf_HC_relIndex_eq_p_pow_q_sec9
      M MF U W1 W2 H0 C p q a hcase
  have hHC_D :
      (HC.subgroupOf M).relIndex (D.subgroupOf M) = u := by
    dsimp [HC, D]
    exact theorem_9_8_HC_subgroupOf_ambientDerived_relIndex_eq_u_sec9
      M MF U W1 W2 H0 C p q a u hcase hBarU
  have hmul :
      (H0C.subgroupOf M).relIndex (HC.subgroupOf M) *
          (HC.subgroupOf M).relIndex (D.subgroupOf M) =
        (H0C.subgroupOf M).relIndex (D.subgroupOf M) :=
    Subgroup.relIndex_mul_relIndex
      (H0C.subgroupOf M) (HC.subgroupOf M) (D.subgroupOf M)
      hH0Cm_le_HCm hHCm_le_Dm
  simpa [D, H0C, hH0C_HC, hHC_D] using hmul.symm


end CFSG.Section9

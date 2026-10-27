module

public import CFSG.RankThree.GF2n.Parrott.A1ModelFacts
public import CFSG.Quasithin.Recognition.U33Defs
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import all CFSG.Quasithin.Recognition.U33Defs

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43

private def z0 : CFSG.Quasithin.Z4StarQ8Model := ⟨2, 0, 0⟩

private theorem pauli_commuting_involutions :
    ∀ x y : CFSG.Quasithin.Z4StarQ8Model, x * x = 1 → y * y = 1 → x * y = y * x →
      x = 1 ∨ x = z0 ∨ y = 1 ∨ y = z0 ∨ y = x ∨ y = x * z0 := by
  decide +kernel

private theorem card_le_four_of_sq_eq_one_pauli {S : Subgroup CFSG.Quasithin.Z4StarQ8Model}
    (hsq : ∀ x ∈ S, x * x = 1) (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    Nat.card S ≤ 4 := by
  classical
  by_cases hx : ∃ x ∈ S, x ≠ 1 ∧ x ≠ z0
  · obtain ⟨x, hxS, hx1, hxz⟩ := hx
    have hsub : (S : Set CFSG.Quasithin.Z4StarQ8Model) ⊆
        ((({1, z0, x, x * z0} : Finset CFSG.Quasithin.Z4StarQ8Model)) : Set _) := by
      intro y hy
      rcases pauli_commuting_involutions x y (hsq x hxS) (hsq y hy) (hcomm x hxS y hy) with
        h | h | h | h | h | h
      · exact absurd h hx1
      · exact absurd h hxz
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
    calc Nat.card S = (S : Set CFSG.Quasithin.Z4StarQ8Model).ncard := Nat.card_coe_set_eq _
      _ ≤ ((({1, z0, x, x * z0} : Finset CFSG.Quasithin.Z4StarQ8Model)) : Set _).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = ({1, z0, x, x * z0} : Finset CFSG.Quasithin.Z4StarQ8Model).card := Set.ncard_coe_finset _
      _ ≤ 4 := Finset.card_le_four
  · push Not at hx
    have hsub : (S : Set CFSG.Quasithin.Z4StarQ8Model) ⊆
        ((({1, z0} : Finset CFSG.Quasithin.Z4StarQ8Model)) : Set _) := by
      intro y hy
      by_cases h1 : y = 1
      · simp [h1]
      · simp [hx y hy h1]
    calc Nat.card S = (S : Set CFSG.Quasithin.Z4StarQ8Model).ncard := Nat.card_coe_set_eq _
      _ ≤ ((({1, z0} : Finset CFSG.Quasithin.Z4StarQ8Model)) : Set _).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = ({1, z0} : Finset CFSG.Quasithin.Z4StarQ8Model).card := Set.ncard_coe_finset _
      _ ≤ 4 := (Finset.card_le_two).trans (by norm_num)

section Model


private noncomputable abbrev ιP : ↥QP45.originalSubgroup →* ↥QA45.originalSubgroup :=
  Subgroup.inclusion QP45_le_QA45

private noncomputable def sP : Subgroup ↥QP45.originalSubgroup := sQA45.comap ιP

private theorem sQA45_le_range : sQA45 ≤ ιP.range := by
  rw [sQA45, Subgroup.closure_le]
  rintro g (rfl | rfl | rfl | rfl)
  · exact ⟨⟨u, u_mem_Q⟩, rfl⟩
  · refine ⟨⟨alpha1, alpha1_mem_Q⟩ * ⟨alpha2, alpha2_mem_Q⟩, ?_⟩
    rw [map_mul]
    rfl
  · refine ⟨⟨beta1, beta1_mem_Q⟩ * ⟨beta2, beta2_mem_Q⟩, ?_⟩
    rw [map_mul]
    rfl
  · exact ⟨⟨t, t_mem_Q⟩, rfl⟩

private theorem card_sP : Nat.card sP = 16 := by
  have h : Nat.card ((sQA45.comap ιP).map ιP) = Nat.card (sQA45.comap ιP) :=
    Nat.card_congr (Subgroup.equivMapOfInjective _ ιP
      (Subgroup.inclusion_injective QP45_le_QA45)).toEquiv.symm
  rw [Subgroup.map_comap_eq_self sQA45_le_range, card_sQA45] at h
  unfold sP
  rw [← h]
  norm_num

private theorem sP_comm : ∀ x ∈ sP, ∀ y ∈ sP, x * y = y * x := by
  intro x hx y hy
  have h := isElemAbelian_sQA45.1.is_comm.comm ⟨ιP x, hx⟩ ⟨ιP y, hy⟩
  apply Subgroup.inclusion_injective QP45_le_QA45
  simpa using congrArg Subtype.val h

private theorem sP_sq : ∀ x ∈ sP, x * x = 1 := by
  intro x hx
  have h := isElemAbelian_sQA45.2 (ιP x) hx
  apply Subgroup.inclusion_injective QP45_le_QA45
  rw [map_mul, map_one, ← pow_two]
  exact h

private theorem u_mem_sP : (⟨u, u_mem_Q⟩ : ↥QP45.originalSubgroup) ∈ sP := by
  change ιP ⟨u, u_mem_Q⟩ ∈ sQA45
  rw [sQA45]
  exact Subgroup.subset_closure (Or.inl rfl)

private theorem t_mem_sP : (⟨t, t_mem_Q⟩ : ↥QP45.originalSubgroup) ∈ sP := by
  change ιP ⟨t, t_mem_Q⟩ ∈ sQA45
  rw [sQA45]
  exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl)))

private theorem sP_le_centralizer :
    sP ≤ Subgroup.centralizer ({(⟨u, u_mem_Q⟩ : ↥QP45.originalSubgroup) * ⟨t, t_mem_Q⟩} :
      Set ↥QP45.originalSubgroup) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := sP_comm x hx _ u_mem_sP
  have h2 := sP_comm x hx _ t_mem_sP
  calc x * (⟨u, u_mem_Q⟩ * ⟨t, t_mem_Q⟩) = (x * ⟨u, u_mem_Q⟩) * ⟨t, t_mem_Q⟩ := by group
    _ = (⟨u, u_mem_Q⟩ * x) * ⟨t, t_mem_Q⟩ := by rw [h1]
    _ = ⟨u, u_mem_Q⟩ * (x * ⟨t, t_mem_Q⟩) := by group
    _ = ⟨u, u_mem_Q⟩ * (⟨t, t_mem_Q⟩ * x) := by rw [h2]
    _ = ⟨u, u_mem_Q⟩ * ⟨t, t_mem_Q⟩ * x := by group

end Model

theorem qp45_no_z4q8_le_centralizer_ut :
    ∀ L : Subgroup ↥QP45.originalSubgroup,
      L ≤ Subgroup.centralizer ({(⟨u, u_mem_Q⟩ : ↥QP45.originalSubgroup) * ⟨t, t_mem_Q⟩} :
        Set ↥QP45.originalSubgroup) →
      ¬ Nonempty (↥L ≃* CFSG.Quasithin.Z4StarQ8Model) := by
  intro L hLC ⟨eL⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({(⟨u, u_mem_Q⟩ : ↥QP45.originalSubgroup) * ⟨t, t_mem_Q⟩} :
    Set ↥QP45.originalSubgroup) with hCdef
  have hC : Nat.card C = 96 := qp45_card_centralizer_ut
  have hL : Nat.card L = 16 := by
    rw [Nat.card_congr eL.toEquiv, Nat.card_eq_fintype_card]
    rfl
  have hL2 : IsPGroup 2 L := IsPGroup.of_card (n := 4) (by rw [hL]; norm_num)
  have hE2 : IsPGroup 2 sP := IsPGroup.of_card (n := 4) (by rw [card_sP]; norm_num)
  obtain ⟨Q, hLQ⟩ := (hL2.comap_subtype (K := C) : IsPGroup 2 (L.subgroupOf C)).exists_le_sylow
  set T : Subgroup ↥QP45.originalSubgroup := (Q : Subgroup C).map C.subtype with hT
  have hTsyl : IsSylowOf 2 T C := ⟨Q, rfl⟩
  have hLT : L ≤ T := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hLC]
    exact Subgroup.map_mono hLQ
  have hTcard : Nat.card T = 32 := by
    rw [hTsyl.card_eq, hC]
    have h : (96 : ℕ) = 2 ^ 5 * 3 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
    norm_num
  have hSsub : IsPGroup 2 (sP.subgroupOf C) := hE2.comap_subtype
  obtain ⟨Q', hSQ'⟩ := hSsub.exists_le_sylow
  set T' : Subgroup ↥QP45.originalSubgroup := (Q' : Subgroup C).map C.subtype with hT'
  have hT'syl : IsSylowOf 2 T' C := ⟨Q', rfl⟩
  have hST' : sP ≤ T' := by
    rw [← Subgroup.map_subgroupOf_eq_of_le sP_le_centralizer]
    exact Subgroup.map_mono hSQ'
  obtain ⟨k, hkC, hk⟩ := hTsyl.exists_mem_conj hT'syl
  set E : Subgroup ↥QP45.originalSubgroup := sP.map (MulAut.conj k⁻¹).toMonoidHom with hE
  have hET : E ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    have := (hk x).mp (hST' hx)
    simpa [MulAut.conj_apply] using this
  have hEcard : Nat.card E = 16 := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, card_sP]
  have hEidx : E.relIndex T = 2 := by
    have h := Subgroup.relIndex_mul_card E T
    rw [inf_eq_left.mpr hET, hEcard, hTcard] at h
    omega
  have hEnorm : (E.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hEidx
  have hTN : T ≤ Subgroup.normalizer (E : Set ↥QP45.originalSubgroup) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hET).mp hEnorm
  have hcard := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (hLT.trans hTN)
  have hsup : Nat.card (L ⊔ E : Subgroup ↥QP45.originalSubgroup) ≤ 32 := by
    rw [← hTcard]
    exact Subgroup.card_le_of_le (sup_le hLT hET)
  rw [hL, hEcard] at hcard
  have hinf : 8 ≤ Nat.card (L ⊓ E : Subgroup ↥QP45.originalSubgroup) := by
    by_contra h
    push Not at h
    have : Nat.card (L ⊔ E : Subgroup ↥QP45.originalSubgroup) *
        Nat.card (L ⊓ E : Subgroup ↥QP45.originalSubgroup) < 32 * 8 :=
      Nat.mul_lt_mul_of_le_of_lt hsup h (by norm_num)
    omega
  have hEsq : ∀ x ∈ E, x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, sP_sq y hy, map_one]
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, sP_comm x hx y hy]
  set N : Subgroup CFSG.Quasithin.Z4StarQ8Model :=
    ((L ⊓ E).subgroupOf L).map eL.toMonoidHom with hN
  have hNcard : Nat.card N = Nat.card (L ⊓ E : Subgroup ↥QP45.originalSubgroup) := by
    rw [hN, Subgroup.card_map_of_injective eL.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hNsq : ∀ x ∈ N, x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have h := hEsq (y : ↥QP45.originalSubgroup) (Subgroup.mem_subgroupOf.mp hy).2
    have hy1 : y * y = 1 := Subtype.ext (by simpa using h)
    rw [← map_mul]
    simp [hy1]
  have hNcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h := hEcomm (x : ↥QP45.originalSubgroup) (Subgroup.mem_subgroupOf.mp hx).2
      (y : ↥QP45.originalSubgroup)
      (Subgroup.mem_subgroupOf.mp hy).2
    have hxy : x * y = y * x := Subtype.ext (by simpa using h)
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hxy]
  have h4 := card_le_four_of_sq_eq_one_pauli hNsq hNcomm
  omega

end CFSG.RankThree.GF2n.Parrott

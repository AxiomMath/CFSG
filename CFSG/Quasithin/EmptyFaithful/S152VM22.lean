module

public import CFSG.Quasithin.EmptyFaithful.S152VSec
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.Quasithin.S152V

open CFSG.Sporadic.Mathieu CFSG.Blueprint

theorem isSimpleGroup_M22 :
    IsSimpleGroup (NativeSporadic.Carrier .M22) :=
  (fam_m22_simplicity).2.2

theorem not_isPGroup_M22 :
    ¬ IsPGroup 2 (NativeSporadic.Carrier .M22) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (NativeSporadic.Carrier .M22) := fam_m22_simplicity.1
  obtain ⟨n, hn⟩ := h.exists_card_eq
  have h1 : Nat.card (NativeSporadic.Carrier .M22) = 443520 := card_M22
  rw [h1] at hn
  have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

def dU : ↥NativeSporadic.M22 := m22a

def dV : ↥NativeSporadic.M22 :=
  m22b * m22a * m22b * m22a * m22b * m22b * m22a * m22b⁻¹ * m22a * m22b⁻¹

theorem dU_sq : dU ^ 2 = 1 := by unfold dU; decide +kernel

theorem dV_sq : dV ^ 2 = 1 := by unfold dV; decide +kernel

theorem dUV_four : (dU * dV) ^ 4 = 1 := by unfold dU dV; decide +kernel

theorem dUV_ne : dU * dV ≠ dV * dU := by unfold dU dV; decide +kernel

theorem exists_nonabelian_two_subgroup_aux :
    ∃ Q : Subgroup ↥NativeSporadic.M22, IsPGroup 2 Q ∧ ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x := by
  have h4 := pow_four_eq_one_of_dihedral dU dV dU_sq dV_sq dUV_four
  refine ⟨Subgroup.closure {dU, dV}, fun q => ⟨2, ?_⟩, dU, Subgroup.subset_closure (by simp), dV,
    Subgroup.subset_closure (by simp), dUV_ne⟩
  exact Subtype.ext (by simpa using h4 q.1 q.2)

def eA : ↥NativeSporadic.M22 := m22b * m22a * m22b * m22a * m22b⁻¹ * m22a * m22b⁻¹

def eB : ↥NativeSporadic.M22 :=
  m22b * m22b * m22a * m22b⁻¹ * m22a * m22b * m22a * m22b * m22b

def eC : ↥NativeSporadic.M22 :=
  m22a * m22b * m22a * m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b * m22a * m22b * m22a * m22b *
    m22a * m22b⁻¹ * m22a

theorem eA_sq : eA ^ 2 = 1 := by unfold eA; decide +kernel

theorem eB_sq : eB ^ 2 = 1 := by unfold eB; decide +kernel

theorem eC_sq : eC ^ 2 = 1 := by unfold eC; decide +kernel

theorem eAB : eA * eB = eB * eA := by unfold eA eB; decide +kernel

theorem eAC : eA * eC = eC * eA := by unfold eA eC; decide +kernel

theorem eBC : eB * eC = eC * eB := by unfold eB eC; decide +kernel

theorem e_nodup : [1, eA, eB, eC, eA * eB, eA * eC, eB * eC, eA * eB * eC].Nodup := by
  unfold eA eB eC; decide +kernel

theorem exists_elemAbelian_eight_aux :
    ∃ E : Subgroup ↥NativeSporadic.M22, (∀ x ∈ E, x ^ 2 = 1) ∧ 8 ≤ Nat.card E := by
  have hsq : ∀ x ∈ ({eA, eB, eC} : Set ↥NativeSporadic.M22), x ^ 2 = 1 := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact eA_sq
    · exact eB_sq
    · exact eC_sq
  have hcomm : ∀ x ∈ ({eA, eB, eC} : Set ↥NativeSporadic.M22),
      ∀ y ∈ ({eA, eB, eC} : Set ↥NativeSporadic.M22), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    exacts [rfl, eAB, eAC, eAB.symm, rfl, eBC, eAC.symm, eBC.symm, rfl]
  refine ⟨Subgroup.closure {eA, eB, eC}, pow_two_eq_one_of_closure _ hsq hcomm, ?_⟩
  set E := Subgroup.closure ({eA, eB, eC} : Set ↥NativeSporadic.M22) with hEdef
  have hA : eA ∈ E := Subgroup.subset_closure (by simp)
  have hB : eB ∈ E := Subgroup.subset_closure (by simp)
  have hC : eC ∈ E := Subgroup.subset_closure (by simp)
  have hmem : ∀ x ∈ [1, eA, eB, eC, eA * eB, eA * eC, eB * eC, eA * eB * eC], x ∈ E := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact E.one_mem
    · exact hA
    · exact hB
    · exact hC
    · exact E.mul_mem hA hB
    · exact E.mul_mem hA hC
    · exact E.mul_mem hB hC
    · exact E.mul_mem (E.mul_mem hA hB) hC
  have hcard : ([1, eA, eB, eC, eA * eB, eA * eC, eB * eC, eA * eB * eC] :
      List ↥NativeSporadic.M22).toFinset.card = 8 := by
    rw [List.toFinset_card_of_nodup e_nodup]
    rfl
  calc 8 = ([1, eA, eB, eC, eA * eB, eA * eC, eB * eC, eA * eB * eC] :
        List ↥NativeSporadic.M22).toFinset.card := hcard.symm
    _ = Nat.card ↥([1, eA, eB, eC, eA * eB, eA * eC, eB * eC, eA * eB * eC] :
        List ↥NativeSporadic.M22).toFinset := by
          rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Nat.card E :=
          Nat.card_le_card_of_injective (fun x => ⟨x.1, hmem x.1 (List.mem_toFinset.1 x.2)⟩)
            (fun x y h => Subtype.ext (congrArg (fun z : E => (z : ↥NativeSporadic.M22)) h))

theorem exists_nonabelian_two_subgroup :
    ∃ Q : Subgroup (NativeSporadic.Carrier .M22), IsPGroup 2 Q ∧ ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x :=
  exists_nonabelian_two_subgroup_aux

theorem exists_elemAbelian_eight :
    ∃ E : Subgroup (NativeSporadic.Carrier .M22), (∀ x ∈ E, x ^ 2 = 1) ∧ 8 ≤ Nat.card E :=
  exists_elemAbelian_eight_aux

end CFSG.Quasithin.S152V

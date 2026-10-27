module

public import CFSG.Sporadic.HeldB.OuterArithCheck

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native Pointwise

@[expose] def heW : Equiv.Perm (Fin 8330) := heGenPerm 0 * heGenPerm 1 ^ 2

theorem rep_hePowA {t : Array ℕ} {g : Equiv.Perm (Fin 8330)} (ht : Rep 8330 t g) :
    ∀ e, Rep 8330 (hePowA t e) (g ^ e)
  | 0 => by
    rw [hePowA, pow_zero]
    exact rep_idA
  | e + 1 => by
    rw [hePowA, pow_succ']
    exact rep_compA ht (rep_hePowA ht e)

theorem rep_heAutR :
    Rep 8330 heAutRArr heAutR := (rep_permOfArr heOuterArith_check.1).1

theorem rep_heU : Rep 8330 heUArr heAutU := rep_hePowA rep_heAutR 5

theorem rep_heW2 : Rep 8330 heW2Arr (heW ^ 2) :=
  rep_hePowA (rep_compA (rep_heGen (by norm_num)) (rep_hePowA (rep_heGen (by norm_num)) 2)) 2

theorem heAutR_pow_ten : heAutR ^ 10 = 1 :=
  eq_of_eqA (rep_hePowA rep_heAutR 10) rep_idA heOuterArith_check.2.1

theorem heAutR_pow_ne
    {e : ℕ} (he : eqA 8330 (hePowA heAutRArr e) (idA 8330) = false) :
    heAutR ^ e ≠ 1 := by
  intro h
  have h' := (eqA_iff (rep_hePowA rep_heAutR e) rep_idA).2 h
  rw [h'] at he
  exact absurd he (by decide)

theorem heAutR_sq_ne_one :
    heAutR ^ 2 ≠ 1 := heAutR_pow_ne heOuterArith_check.2.2.1

theorem heAutR_pow_five_ne_one :
    heAutR ^ 5 ≠ 1 := heAutR_pow_ne heOuterArith_check.2.2.2.1

theorem orderOf_heAutR : orderOf heAutR = 10 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) heAutR_pow_ten fun p hp hpd => ?_
  have hp' : p = 2 ∨ p = 5 := by
    have h := (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 5 from hpd)
    rcases h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h)
  rcases hp' with rfl | rfl
  · exact heAutR_pow_five_ne_one
  · exact heAutR_sq_ne_one

theorem heAutR_conj_a0 :
    heAutR * heGenPerm 0 * heAutR⁻¹ = heGenPerm 0 := by
  have h := eq_of_eqA (rep_compA rep_heAutR (rep_heGen (by norm_num)))
    (rep_compA (rep_heGen (by norm_num)) rep_heAutR) heOuterArith_check.2.2.2.2.1
  rw [h, mul_inv_cancel_right]

theorem heAutR_conj_a1 :
    heAutR * heGenPerm 1 * heAutR⁻¹ = (heW ^ 2)⁻¹ * heGenPerm 1 * heW ^ 2 := by
  have h := eq_of_eqA (rep_compA rep_heW2 (rep_compA rep_heAutR (rep_heGen (by norm_num))))
    (rep_compA (rep_heGen (by norm_num)) (rep_compA rep_heW2 rep_heAutR))
    heOuterArith_check.2.2.2.2.2.1
  calc heAutR * heGenPerm 1 * heAutR⁻¹
      = (heW ^ 2)⁻¹ * (heW ^ 2 * (heAutR * heGenPerm 1)) * heAutR⁻¹ := by group
    _ = (heW ^ 2)⁻¹ * (heGenPerm 1 * (heW ^ 2 * heAutR)) * heAutR⁻¹ := by rw [h]
    _ = (heW ^ 2)⁻¹ * heGenPerm 1 * heW ^ 2 := by group

theorem heAutR_not_mem :
    heAutR ∉ heP := fun h =>
  absurd ((mem_heP_iff_siftA rep_heAutR).2 h) (by rw [heOuterArith_check.2.2.2.2.2.2.1]; decide)

theorem heAutR_sq_mem :
    heAutR ^ 2 ∈ heP :=
  (mem_heP_iff_siftA (rep_hePowA rep_heAutR 2)).1 heOuterArith_check.2.2.2.2.2.2.2

theorem heW_mem : heW ∈ heP :=
  heP.mul_mem (heGenPerm_mem (by norm_num)) (heP.pow_mem (heGenPerm_mem (by norm_num)) 2)

theorem heP_map_conj_le :
    heP.map (MulAut.conj heAutR).toMonoidHom ≤ heP := by
  rw [heP, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  rcases hg with rfl | rfl
  · change heAutR * heGenPerm 0 * heAutR⁻¹ ∈ _
    rw [heAutR_conj_a0]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · change heAutR * heGenPerm 1 * heAutR⁻¹ ∈ _
    rw [heAutR_conj_a1, ← heP]
    exact heP.mul_mem (heP.mul_mem (heP.inv_mem (heP.pow_mem heW_mem 2))
      (heGenPerm_mem (by norm_num))) (heP.pow_mem heW_mem 2)

theorem heP_map_conj :
    heP.map (MulAut.conj heAutR).toMonoidHom = heP := by
  apply Subgroup.eq_of_le_of_card_ge heP_map_conj_le
  rw [Subgroup.card_map_of_injective (MulAut.conj heAutR).injective]

theorem heAutR_mem_normalizer :
    heAutR ∈ Subgroup.normalizer (heP : Set (Equiv.Perm (Fin 8330))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact heP_map_conj_le ⟨h, hh, rfl⟩
  · intro hh
    rw [← heP_map_conj] at hh
    obtain ⟨k, hk, hkh⟩ := hh
    have : k = h := by
      have := hkh
      change heAutR * k * heAutR⁻¹ = heAutR * h * heAutR⁻¹ at this
      simpa using this
    rwa [← this]

theorem heAutU_mem_normalizer :
    heAutU ∈ Subgroup.normalizer (heP : Set (Equiv.Perm (Fin 8330))) :=
  Subgroup.pow_mem _ heAutR_mem_normalizer 5

theorem heAutU_sq : heAutU ^ 2 = 1 := by
  rw [heAutU, ← pow_mul]
  exact heAutR_pow_ten

theorem orderOf_heAutU : orderOf heAutU = 2 :=
  orderOf_eq_prime heAutU_sq heAutR_pow_five_ne_one

theorem heAutU_not_mem :
    heAutU ∉ heP := by
  intro hu
  apply heAutR_not_mem
  have h4 : heAutR ^ 4 ∈ heP := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    exact heP.pow_mem heAutR_sq_mem 2
  have : heAutR = heAutU * (heAutR ^ 4)⁻¹ := by
    rw [heAutU, eq_mul_inv_iff_mul_eq, ← pow_succ']
  rw [this]
  exact heP.mul_mem hu (heP.inv_mem h4)

theorem heP_le_heAutGroup : heP ≤ heAutGroup := le_sup_left

theorem heAutU_mem_heAutGroup : heAutU ∈ heAutGroup :=
  (le_sup_right : Subgroup.zpowers heAutU ≤ heAutGroup) (Subgroup.mem_zpowers _)

theorem zpowers_heAutU_le_normalizer :
    Subgroup.zpowers heAutU ≤ Subgroup.normalizer (heP : Set (Equiv.Perm (Fin 8330))) :=
  (Subgroup.zpowers_le).2 heAutU_mem_normalizer

theorem heAutGroup_le_normalizer :
    heAutGroup ≤ Subgroup.normalizer (heP : Set (Equiv.Perm (Fin 8330))) :=
  sup_le Subgroup.le_normalizer zpowers_heAutU_le_normalizer

theorem heP_normal_heAutGroup :
    (heP.subgroupOf heAutGroup).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer heP_le_heAutGroup).2 heAutGroup_le_normalizer

theorem heAutGroup_coe :
    (heAutGroup : Set (Equiv.Perm (Fin 8330))) =
      (heP : Set (Equiv.Perm (Fin 8330))) *
        (↑(Subgroup.zpowers heAutU) : Set (Equiv.Perm (Fin 8330))) :=
  Subgroup.coe_mul_of_right_le_normalizer_left heP _ zpowers_heAutU_le_normalizer

theorem heAutU_zpow_mem
    (k : ℤ) : heAutU ^ k = 1 ∨ heAutU ^ k = heAutU := by
  rw [← zpow_mod_orderOf, orderOf_heAutU]
  have h : k % (2 : ℕ) = 0 ∨ k % (2 : ℕ) = 1 := by omega
  rcases h with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

theorem mem_heAutGroup_cases
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heAutGroup) :
    x ∈ heP ∨ x * heAutU ∈ heP := by
  have hx' : x ∈ (heAutGroup : Set (Equiv.Perm (Fin 8330))) := hx
  rw [heAutGroup_coe] at hx'
  obtain ⟨p, hp, v, hv, rfl⟩ := hx'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
  rcases heAutU_zpow_mem k with h | h
  · left
    show p * heAutU ^ k ∈ heP
    rw [h, mul_one]
    exact hp
  · right
    show p * heAutU ^ k * heAutU ∈ heP
    rw [h, mul_assoc, ← sq, heAutU_sq, mul_one]
    exact hp

theorem heP_relIndex_heAutGroup :
    heP.relIndex heAutGroup = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨⟨heAutU, heAutU_mem_heAutGroup⟩, ?_, fun b => ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact heAutU_not_mem
  · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rcases mem_heAutGroup_cases b.2 with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem ctbh_exact_outer_involution_arithmetic :
    (heAutRArr.size = 8330 ∧ (∀ i < 8330, heAutRArr[i]! < 8330) ∧
      (∀ i < 8330, ∀ j < 8330, heAutRArr[i]! = heAutRArr[j]! → i = j) ∧
      Rep 8330 heAutRArr heAutR) ∧
    orderOf heAutR = 10 ∧ heAutR * heGenPerm 0 * heAutR⁻¹ = heGenPerm 0 ∧
    heAutR * heGenPerm 1 * heAutR⁻¹ = (heW ^ 2)⁻¹ * heGenPerm 1 * heW ^ 2 ∧
    heAutR ∉ heP ∧ heAutR ^ 2 ∈ heP ∧
    heAutR ∈ Subgroup.normalizer (heP : Set (Equiv.Perm (Fin 8330))) ∧
    orderOf heAutU = 2 ∧ heAutU ∉ heP ∧
    heP ≤ heAutGroup ∧ (heP.subgroupOf heAutGroup).Normal ∧
    (heAutGroup : Set (Equiv.Perm (Fin 8330))) =
      (heP : Set (Equiv.Perm (Fin 8330))) *
        (↑(Subgroup.zpowers heAutU) : Set (Equiv.Perm (Fin 8330))) ∧
    heP.relIndex heAutGroup = 2 := by
  have hinv := heOuterArith_check.1
  refine ⟨⟨by simp [heAutRArr, hexTable], fun i hi => (isInvA_spec hinv hi).1,
    fun i hi j hj hij => ?_, rep_heAutR⟩, orderOf_heAutR, heAutR_conj_a0, heAutR_conj_a1,
    heAutR_not_mem, heAutR_sq_mem, heAutR_mem_normalizer, orderOf_heAutU, heAutU_not_mem,
    heP_le_heAutGroup, heP_normal_heAutGroup, heAutGroup_coe, heP_relIndex_heAutGroup⟩
  rw [← (isInvA_spec hinv hi).2, ← (isInvA_spec hinv hj).2, hij]

end CFSG.Sporadic.HeldB

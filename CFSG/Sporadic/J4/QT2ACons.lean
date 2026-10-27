module

public import CFSG.Sporadic.J4.QT2ASyl

public section

namespace CFSG.Sporadic.J4.QT2A

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix

theorem prime_dvd_cz {r : ℕ} (hr : r.Prime) (h : r ∣ 21799895040) :
    r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 11 := by
  have e : (21799895040 : ℕ) = 2 ^ 21 * (3 ^ 3 * (5 * (7 * 11))) := by norm_num
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  · right
    rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hr.dvd_of_dvd_pow h))
    · right
      rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h)
      · right
        rcases (Nat.Prime.dvd_mul hr).1 h with h | h
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h)
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h)

theorem chkWit_parts :
    wfR (qR 0) = true ∧ (∀ n < 27, n ≠ 0 → nocomm (qR 0) (yEl n) = true) ∧
    (∀ k < 4, nocomm (qR 0) (powRows (y5R ()) (k + 1)) = true) ∧
    (∀ k < 6, nocomm (qR 0) (powRows (y7R ()) (k + 1)) = true) ∧
    (∀ k < 10, nocomm (qR 0) (powRows (y11R ()) (k + 1)) = true) := by
  have h := chkWit_true
  unfold chkWit at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hw, h1⟩, h2⟩, h3⟩, h4⟩ := h
  refine ⟨hw, fun n hn hn0 => ?_, h2, h3, h4⟩
  rcases Bool.or_eq_true_iff.1 (h1 n hn) with h | h
  · exact absurd (beq_iff_eq.1 h) hn0
  · exact h

section Cons

variable (hM : MatFacts)
include hM

theorem yJ_notMem_Qz {n : ℕ} (hn : n < 27) (hn0 : n ≠ 0) : yJ n ∉ Qz := by
  have h := chkNotQzY_true
  unfold chkNotQzY at h
  have h1 := List.all_eq_true.1 h n (List.mem_range.2 hn)
  rcases Bool.or_eq_true_iff.1 h1 with h2 | h2
  · exact absurd (beq_iff_eq.1 h2) hn0
  · exact not_mem_Qz_of_notQz hM (Mx_yJ hM n) h2

theorem Ycl_nonid_notMem_Qz : ∀ y ∈ Ycl, y ≠ 1 → y ∉ Qz := by
  intro y hy hy1
  obtain ⟨n, hn, rfl⟩ := Ycl_subset hM hy
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hy1 yJ_zero
  exact yJ_notMem_Qz hM hn hn0

theorem isPGroup_two_of_sylows
    (hC : Nat.card Cz = 21799895040) {M : Subgroup J} (hMC : M ≤ Cz)
    (hMn : ∀ c ∈ Cz, ∀ m ∈ M, c * m * c⁻¹ ∈ M) (h3 : ∀ y ∈ Ycl, y ≠ 1 → y ∉ M)
    (h5 : ∀ k, 1 ≤ k → k < 5 → y5J ^ k ∉ M) (h7 : ∀ k, 1 ≤ k → k < 7 → y7J ^ k ∉ M)
    (h11 : ∀ k, 1 ≤ k → k < 11 → y11J ^ k ∉ M) : IsPGroup 2 M := by
  refine isPGroup_two_of_no_odd_prime fun r hr hr2 hrM => ?_
  have hdvd : r ∣ 21799895040 := by
    rw [← hC]
    exact hrM.trans (Subgroup.card_dvd_of_le hMC)
  have : Fact r.Prime := ⟨hr⟩
  rcases prime_dvd_cz hr hdvd with rfl | rfl | rfl | rfl | rfl
  · exact hr2 rfl
  ·
    refine not_dvd_card_of_sylow_sub 3 Cz Ycl M (Ycl_le_Cz hM) hMC
      (IsPGroup.of_card (n := 3) (by rw [card_Ycl hM]; norm_num)) ?_ hMn h3 hrM
    have h := relIndex_mul_card_of_le (Ycl_le_Cz hM)
    rw [card_Ycl hM, hC] at h
    have : Ycl.relIndex Cz = 807403520 := by omega
    rw [this]
    norm_num
  ·
    have hy := (y_prime_facts hM (Mx_y5J hM) chkYr5_true : _ ∧ orderOf y5J = 5)
    refine not_dvd_card_of_sylow_sub 5 Cz (Subgroup.zpowers y5J) M ?_ hMC ?_ ?_ hMn ?_ hrM
    · rw [Subgroup.zpowers_le]; exact hy.1
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy.2, pow_one])
    · have h := relIndex_mul_card_of_le (C := Cz) (Y := Subgroup.zpowers y5J)
        (by rw [Subgroup.zpowers_le]; exact hy.1)
      rw [Nat.card_zpowers, hy.2, hC] at h
      have : (Subgroup.zpowers y5J).relIndex Cz = 4359979008 := by omega
      rw [this]
      norm_num
    · intro y hy' hy1
      obtain ⟨k, hk1, hk, rfl⟩ := zpowers_nonid hy' hy1
      rw [hy.2] at hk
      exact h5 k hk1 hk
  ·
    have hy := (y_prime_facts hM (Mx_y7J hM) chkYr7_true : _ ∧ orderOf y7J = 7)
    refine not_dvd_card_of_sylow_sub 7 Cz (Subgroup.zpowers y7J) M ?_ hMC ?_ ?_ hMn ?_ hrM
    · rw [Subgroup.zpowers_le]; exact hy.1
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy.2, pow_one])
    · have h := relIndex_mul_card_of_le (C := Cz) (Y := Subgroup.zpowers y7J)
        (by rw [Subgroup.zpowers_le]; exact hy.1)
      rw [Nat.card_zpowers, hy.2, hC] at h
      have : (Subgroup.zpowers y7J).relIndex Cz = 3114270720 := by omega
      rw [this]
      norm_num
    · intro y hy' hy1
      obtain ⟨k, hk1, hk, rfl⟩ := zpowers_nonid hy' hy1
      rw [hy.2] at hk
      exact h7 k hk1 hk
  ·
    have hy := (y_prime_facts hM (Mx_y11J hM) chkYr11_true : _ ∧ orderOf y11J = 11)
    refine not_dvd_card_of_sylow_sub 11 Cz (Subgroup.zpowers y11J) M ?_ hMC ?_ ?_ hMn ?_ hrM
    · rw [Subgroup.zpowers_le]; exact hy.1
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy.2, pow_one])
    · have h := relIndex_mul_card_of_le (C := Cz) (Y := Subgroup.zpowers y11J)
        (by rw [Subgroup.zpowers_le]; exact hy.1)
      rw [Nat.card_zpowers, hy.2, hC] at h
      have : (Subgroup.zpowers y11J).relIndex Cz = 1981808640 := by omega
      rw [this]
      norm_num
    · intro y hy' hy1
      obtain ⟨k, hk1, hk, rfl⟩ := zpowers_nonid hy' hy1
      rw [hy.2] at hk
      exact h11 k hk1 hk

@[expose] noncomputable def CQ : Subgroup J := Cz ⊓ Subgroup.centralizer (Qz : Set J)

omit hM in
theorem CQ_le_Cz : CQ ≤ Cz := inf_le_left

omit hM in
theorem CQ_conj {c : J} (hc : c ∈ Cz) {m : J} (hm : m ∈ CQ) : c * m * c⁻¹ ∈ CQ := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hm.1) (Subgroup.inv_mem _ hc),
    Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
  have hq' : c⁻¹ * q * c ∈ Qz := by
    have := Qz_conj (Subgroup.inv_mem _ hc) hq
    simpa using this
  have hcomm := Subgroup.mem_centralizer_iff.1 hm.2 (c⁻¹ * q * c) hq'
  calc q * (c * m * c⁻¹) = c * ((c⁻¹ * q * c) * m) * c⁻¹ := by group
    _ = c * (m * (c⁻¹ * q * c)) * c⁻¹ := by rw [hcomm]
    _ = c * m * c⁻¹ * q := by group

theorem isPGroup_Qz
    (hC : Nat.card Cz = 21799895040) : IsPGroup 2 Qz := by
  refine isPGroup_two_of_sylows hM hC Qz_le_Cz (fun c hc m hm => Qz_conj hc hm)
    (Ycl_nonid_notMem_Qz hM) ?_ ?_ ?_
  · intro k hk1 hk
    exact pow_notMem_Qz hM (Mx_y5J hM) chkNotQz5_true hk1 hk
  · intro k hk1 hk
    exact pow_notMem_Qz hM (Mx_y7J hM) chkNotQz7_true hk1 hk
  · intro k hk1 hk
    exact pow_notMem_Qz hM (Mx_y11J hM) chkNotQz11_true hk1 hk

theorem q0_mem_Qz : qJ 0 ∈ Qz := qJ_mem_Qz hM (by norm_num)

theorem isPGroup_CQ
    (hC : Nat.card Cz = 21799895040) : IsPGroup 2 CQ := by
  obtain ⟨hw, hY, h5, h7, h11⟩ := chkWit_parts
  have hq0 := q0_mem_Qz hM
  have hcom : ∀ {y : J}, y ∈ CQ → qJ 0 * y = y * qJ 0 := fun hy =>
    Subgroup.mem_centralizer_iff.1 hy.2 (qJ 0) hq0
  refine isPGroup_two_of_sylows hM hC CQ_le_Cz (fun c hc m hm => CQ_conj hc hm) ?_ ?_ ?_ ?_
  · intro y hy hy1 hyM
    obtain ⟨n, hn, rfl⟩ := Ycl_subset hM hy
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hy1 yJ_zero
    obtain ⟨-, -, -, -, -, hwf, -⟩ := chkY_parts
    exact nocomm_ne (Mx_qJ hM 0) (Mx_yJ hM n) hw (hwf n hn) (hY n hn hn0) (hcom hyM)
  · intro k hk1 hk hyM
    have hwf := (chkYr_parts chkYr5_true).2.1
    exact nocomm_ne (Mx_qJ hM 0) (show Mx (y5J ^ k) = rowsMatrix (powRows (y5R ()) k) by
        rw [map_pow, Mx_y5J hM, rowsMatrix_powRows]) hw (wfR_powRows hwf k)
      (by simpa [Nat.sub_add_cancel hk1] using h5 (k - 1) (by omega)) (hcom hyM)
  · intro k hk1 hk hyM
    have hwf := (chkYr_parts chkYr7_true).2.1
    exact nocomm_ne (Mx_qJ hM 0) (show Mx (y7J ^ k) = rowsMatrix (powRows (y7R ()) k) by
        rw [map_pow, Mx_y7J hM, rowsMatrix_powRows]) hw (wfR_powRows hwf k)
      (by simpa [Nat.sub_add_cancel hk1] using h7 (k - 1) (by omega)) (hcom hyM)
  · intro k hk1 hk hyM
    have hwf := (chkYr_parts chkYr11_true).2.1
    exact nocomm_ne (Mx_qJ hM 0) (show Mx (y11J ^ k) = rowsMatrix (powRows (y11R ()) k) by
        rw [map_pow, Mx_y11J hM, rowsMatrix_powRows]) hw (wfR_powRows hwf k)
      (by simpa [Nat.sub_add_cancel hk1] using h11 (k - 1) (by omega)) (hcom hyM)

omit hM in
theorem Cz_le_normalizer_Qz : Cz ≤ Subgroup.normalizer Qz := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact Qz_conj hc hh
  · intro hh
    have := Qz_conj (Subgroup.inv_mem _ hc) hh
    simpa [mul_assoc] using this

theorem exists_normal_two_group_selfcentralizing
    (hC : Nat.card Cz = 21799895040) :
    ∃ N : Subgroup J, N ≤ Cz ∧ (∀ c ∈ Cz, ∀ n ∈ N, c * n * c⁻¹ ∈ N) ∧ IsPGroup 2 N ∧
      ∀ q ∈ Cz, (∀ n ∈ N, q * n = n * q) → q ∈ N := by
  refine ⟨Qz ⊔ CQ, sup_le Qz_le_Cz CQ_le_Cz, ?_, ?_, ?_⟩
  · intro c hc n hn
    exact conj_mem_sup Qz CQ c (fun a ha => Subgroup.mem_sup_left (Qz_conj hc ha))
      (fun b hb => Subgroup.mem_sup_right (CQ_conj hc hb)) n hn
  · exact IsPGroup.to_sup_of_normal_left' (isPGroup_Qz hM hC) (isPGroup_CQ hM hC)
      (CQ_le_Cz.trans Cz_le_normalizer_Qz)
  · intro q hq h
    have : q ∈ CQ := ⟨hq, Subgroup.mem_centralizer_iff.2 fun n hn =>
      (h n (Subgroup.mem_sup_left hn)).symm⟩
    exact Subgroup.mem_sup_right this

end Cons

end CFSG.Sporadic.J4.QT2A

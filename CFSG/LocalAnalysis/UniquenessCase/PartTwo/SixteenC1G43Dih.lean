module

public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
public import CFSG.GH74.SmallRanks.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

private lemma s16c1G43_conj_pow_s {Λ : Type} [Group Λ] {s t : Λ} (hs : s * s = 1)
    (ht : t * t = 1) (k : ℕ) : s * (s * t) ^ k * s = ((s * t) ^ k)⁻¹ := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hconj : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
    rw [hsi, ← mul_assoc s s t, hs, one_mul, mul_inv_rev, hsi, hti]
  have h : (s * (s * t) * s⁻¹) ^ (k : ℤ) = s * (s * t) ^ (k : ℤ) * s⁻¹ :=
    conj_zpow (a := s) (b := s * t) (i := (k : ℤ))
  rw [hconj] at h
  rw [inv_zpow] at h
  rw [zpow_natCast] at h
  rw [hsi] at h
  exact h.symm

private lemma s16c1G43_conj_pow_s' {Λ : Type} [Group Λ] {s t : Λ} (hs : s * s = 1)
    (ht : t * t = 1) (k : ℕ) :
    ((s * t) ^ k)⁻¹ * s * (s * t) ^ k = s * (s * t) ^ (2 * k) := by
  have hB := s16c1G43_conj_pow_s hs ht k
  calc ((s * t) ^ k)⁻¹ * s * (s * t) ^ k
      = (s * (s * t) ^ k * s) * s * (s * t) ^ k := by rw [← hB]
    _ = s * (s * t) ^ k * (s * s) * (s * t) ^ k := by group
    _ = s * (s * t) ^ k * (s * t) ^ k := by rw [hs, mul_one]
    _ = s * ((s * t) ^ k * (s * t) ^ k) := by group
    _ = s * (s * t) ^ (2 * k) := by rw [← pow_add, ← two_mul]

private lemma s16c1G43_conj_pow_t {Λ : Type} [Group Λ] {s t : Λ} (hs : s * s = 1)
    (ht : t * t = 1) (k : ℕ) :
    ((s * t) ^ k)⁻¹ * t * (s * t) ^ k = s * (s * t) ^ (2 * k + 1) := by
  have ht_eq : t = s * (s * t) := by rw [← mul_assoc, hs, one_mul]
  have hB := s16c1G43_conj_pow_s' hs ht k
  calc ((s * t) ^ k)⁻¹ * t * (s * t) ^ k
      = ((s * t) ^ k)⁻¹ * (s * (s * t)) * (s * t) ^ k := by
        conv_lhs => enter [1, 2]; rw [ht_eq]
    _ = ((s * t) ^ k)⁻¹ * s * ((s * t) * (s * t) ^ k) := by simp only [mul_assoc]
    _ = ((s * t) ^ k)⁻¹ * s * (s * t) ^ (k + 1) := by rw [← pow_succ']
    _ = ((s * t) ^ k)⁻¹ * s * ((s * t) ^ k * (s * t)) := by rw [pow_succ]
    _ = (((s * t) ^ k)⁻¹ * s * (s * t) ^ k) * (s * t) := by simp only [mul_assoc]
    _ = (s * (s * t) ^ (2 * k)) * (s * t) := by rw [hB]
    _ = s * ((s * t) ^ (2 * k) * (s * t)) := by simp only [mul_assoc]
    _ = s * (s * t) ^ (2 * k + 1) := by rw [← pow_succ]

private lemma s16c1G43_isConj_s_of_even {Λ : Type} [Group Λ] {s t : Λ} (hs : s * s = 1)
    (ht : t * t = 1) {k : ℕ} (hk : Even k) : IsConj s (s * (s * t) ^ k) := by
  obtain ⟨j, rfl⟩ := even_iff_exists_two_mul.mp hk
  refine isConj_iff.2 ⟨((s * t) ^ j)⁻¹, ?_⟩
  rw [inv_inv, s16c1G43_conj_pow_s' hs ht j]

private lemma s16c1G43_isConj_t_of_odd {Λ : Type} [Group Λ] {s t : Λ} (hs : s * s = 1)
    (ht : t * t = 1) {k : ℕ} (hk : Odd k) : IsConj t (s * (s * t) ^ k) := by
  obtain ⟨j, rfl⟩ := hk
  refine isConj_iff.2 ⟨((s * t) ^ j)⁻¹, ?_⟩
  rw [inv_inv, s16c1G43_conj_pow_t hs ht j]

theorem s16c1G43_dih {Λ : Type} [Group Λ] [Finite Λ] {s t : Λ} (hs : s * s = 1) (ht : t * t = 1)
    (hs1 : s ≠ 1) (ht1 : t ≠ 1) (hgen : Subgroup.closure ({s, t} : Set Λ) = ⊤)
    (hrig : ∀ x y : Λ, (IsConj s x ∨ IsConj t x) → (IsConj s y ∨ IsConj t y) →
      x * y = y * x → x = y) :
    ∃ m : ℕ, Odd m ∧ Nonempty (Λ ≃* DihedralGroup m) ∧ IsConj s t := by
  have hodd : Odd (orderOf (s * t)) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp heven
    set z : Λ := (s * t) ^ k with hz_def
    have hkpos : 0 < k := by
      have h2 : 0 < 2 * k := hk ▸ orderOf_pos (s * t)
      omega
    have hklt : k < orderOf (s * t) := by rw [hk]; omega
    have hz_ne : z ≠ 1 := by
      rw [hz_def]
      exact pow_ne_one_of_lt_orderOf hkpos.ne' hklt
    have hz2 : z * z = 1 := by
      rw [hz_def, ← pow_add, ← two_mul, ← hk, pow_orderOf_eq_one]
    have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    have hz_inv' : ((s * t) ^ k)⁻¹ = (s * t) ^ k := by rw [← hz_def]; exact hz_inv
    have hsz : s * z * s = z := by
      rw [hz_def, s16c1G43_conj_pow_s hs ht k, hz_inv']
    have hcomm_sz : s * z = z * s := by
      apply mul_right_cancel (b := s)
      rw [hsz, mul_assoc, hs, mul_one]
    have hy_conj : IsConj s (s * z) ∨ IsConj t (s * z) := by
      rcases Nat.even_or_odd k with hk_even | hk_odd
      · left
        rw [hz_def]
        exact s16c1G43_isConj_s_of_even hs ht hk_even
      · right
        rw [hz_def]
        exact s16c1G43_isConj_t_of_odd hs ht hk_odd
    have hxy_comm : s * (s * z) = (s * z) * s := by
      rw [← mul_assoc, hs, one_mul, hcomm_sz, mul_assoc, hs, mul_one]
    have hrig_app : s = s * z := hrig s (s * z) (Or.inl (IsConj.refl s)) hy_conj hxy_comm
    have hz1 : z = 1 := by
      have h' : s * 1 = s * z := by rw [mul_one]; exact hrig_app
      exact (mul_left_cancel h').symm
    exact hz_ne hz1
  refine ⟨orderOf (s * t), hodd, ?_, ?_⟩
  · exact (TauCeti.nonempty_dihedralGroup_mulEquiv hs ht hs1 ht1 rfl hgen).map MulEquiv.symm
  · obtain ⟨k, hk⟩ := hodd
    refine isConj_iff.2 ⟨((s * t) ^ (k + 1))⁻¹, ?_⟩
    rw [inv_inv, s16c1G43_conj_pow_s' hs ht (k + 1)]
    have hexp : 2 * (k + 1) = orderOf (s * t) + 1 := by rw [hk]; ring
    rw [hexp, pow_succ, pow_orderOf_eq_one, one_mul, ← mul_assoc, hs, one_mul]

theorem s16c1G43_twoRank_dihedral {Λ : Type} [Group Λ] [Finite Λ] {m : ℕ} (hm : Odd m)
    (e : Λ ≃* DihedralGroup m) : CFSG.Open.twoRank Λ = 1 := by
  haveI : NeZero m := ⟨by obtain ⟨k, hk⟩ := hm; omega⟩
  rw [CFSG.GH74.twoRank_eq_of_mulEquiv e]
  apply IsGreatest.csSup_eq
  refine ⟨⟨Subgroup.zpowers (DihedralGroup.sr 0), le_top,
    ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h2 : (DihedralGroup.sr (0 : ZMod m)) ^ 2 = 1 := by
      rw [sq]; exact DihedralGroup.sr_mul_self 0
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]
  · rw [Nat.card_zpowers, DihedralGroup.orderOf_sr, pow_one]
  · rintro k ⟨E, -, -, hEcard⟩
    have hdvd : 2 ^ k ∣ 2 * m := by
      rw [← hEcard, ← DihedralGroup.nat_card]
      exact Subgroup.card_subgroup_dvd_card E
    by_contra hk
    push Not at hk
    have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk
    have : 4 ∣ 2 * m := (by simpa using h4 : 4 ∣ 2 ^ k).trans hdvd
    have h2 : 2 ∣ m := by omega
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

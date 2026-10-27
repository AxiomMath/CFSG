module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

open Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem three_pow_sub_one_dvd_of_pow_three_eq_one_mod {v k : ℕ} (hv : 2 ≤ v) (hk : 1 ≤ k)
    (h : 3 ^ v ∣ k ^ 3 - 1) : 3 ^ (v - 1) ∣ k - 1 := by
  have h3 : 3 ∣ k ^ 3 - 1 := dvd_trans (dvd_pow_self 3 (by omega : v ≠ 0)) h
  have hc1 : 1 ≤ k ^ 3 := Nat.one_le_pow _ _ hk
  have hcmod : k ^ 3 % 3 = 1 := by omega
  have hk3 : k % 3 = 1 := by
    have hmod : k ^ 3 % 3 = (k % 3) ^ 3 % 3 := Nat.pow_mod k 3 3
    rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
    · simp [h0] at hmod
      omega
    · exact h1
    · simp [h2] at hmod
      omega
  obtain ⟨t, rfl⟩ : ∃ t, k = 3 * t + 1 := ⟨k / 3, by omega⟩
  have hexp : (3 * t + 1) ^ 3 - 1 = 3 ^ 2 * (t * (1 + 3 * t + 3 * t ^ 2)) := by
    have hc : (3 * t + 1) ^ 3 = 3 ^ 2 * (t * (1 + 3 * t + 3 * t ^ 2)) + 1 := by ring
    rw [hc, Nat.add_sub_cancel]
  have e3 : 3 ^ v = 3 ^ 2 * 3 ^ (v - 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hexp, e3] at h
  have h' : 3 ^ (v - 2) ∣ t * (1 + 3 * t + 3 * t ^ 2) :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  have hnd : ¬ 3 ∣ (1 + 3 * t + 3 * t ^ 2) := by
    omega
  have hcop : Nat.Coprime (3 ^ (v - 2)) (1 + 3 * t + 3 * t ^ 2) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd)
  have ht : 3 ^ (v - 2) ∣ t := Nat.Coprime.dvd_of_dvd_mul_right hcop h'
  have e4 : 3 ^ (v - 1) = 3 ^ (v - 2) * 3 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [e4, show 3 * t + 1 - 1 = 3 * t by omega, mul_comm (3 ^ (v - 2)) 3]
  exact mul_dvd_mul_left 3 ht

theorem exists_z_of_cyclic {X : Type} [Group X] [Finite X] (φ : MulAut X) (hφ3 : φ ^ 3 = 1)
    (P : Subgroup X) [IsCyclic P] {v : ℕ} (hv : 2 ≤ v) (hPcard : Nat.card P = 3 ^ v)
    (hPφ : ∀ x ∈ P, φ x ∈ P) {d : X} (hdP : d ∈ P) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hmove : ∃ y ∈ P, φ y ≠ y) :
    ∃ (z : X) (k : ℕ), z ∈ P ∧ orderOf z = 3 ^ v ∧ z ^ 3 ^ (v - 1) = d ∧ φ z = z ^ k ∧
      3 ^ (v - 1) ∣ k - 1 ∧ ¬ 3 ^ v ∣ k - 1 := by
  obtain ⟨g0, hg0P, hg0ord, hgen⟩ : ∃ g0 : X, g0 ∈ P ∧ orderOf g0 = 3 ^ v ∧
      ∀ x ∈ P, x ∈ Subgroup.zpowers g0 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P)
    refine ⟨(g : X), g.2, ?_, ?_⟩
    · rw [orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hPcard]
    · intro x hx
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      refine mem_zpowers_iff.mpr ⟨n, ?_⟩
      have h := congrArg Subtype.val hn
      simpa using h
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hgen d hdP)
  have hn3 : g0 ^ (n * 3) = 1 := by
    rw [zpow_mul, hn]
    simpa using hd3
  have hdvd : ((orderOf g0 : ℕ) : ℤ) ∣ n * 3 := orderOf_dvd_iff_zpow_eq_one.mpr hn3
  rw [hg0ord] at hdvd
  push_cast at hdvd
  have e3 : (3 : ℤ) ^ v = 3 ^ (v - 1) * 3 := by
    rw [← pow_succ]
    congr 1
    omega
  have hdvd' : (3 : ℤ) ^ (v - 1) ∣ n := by
    rw [e3] at hdvd
    exact (mul_dvd_mul_iff_right (by norm_num : (3 : ℤ) ≠ 0)).mp hdvd
  obtain ⟨j, hj⟩ := hdvd'
  have hj3 : ¬ (3 : ℤ) ∣ j := by
    rintro ⟨i, rfl⟩
    apply hd1
    rw [← hn]
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rw [hg0ord]
    push_cast
    rw [hj, e3]
    exact ⟨i, by ring⟩
  have hcop : Nat.Coprime (3 ^ v) j.natAbs := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    apply hj3
    exact_mod_cast Int.natCast_dvd.mpr h
  have hzord : orderOf (g0 ^ j) = 3 ^ v := by
    rw [orderOf_zpow, hg0ord, Nat.Coprime.gcd_eq_one hcop, Nat.div_one]
  have hzmem : g0 ^ j ∈ P := P.zpow_mem hg0P j
  have hzP : Subgroup.zpowers (g0 ^ j) = P := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr hzmem
    · rw [Nat.card_zpowers, hzord, hPcard]
  have hzd : (g0 ^ j) ^ 3 ^ (v - 1) = d := by
    rw [← zpow_natCast (g0 ^ j) (3 ^ (v - 1)), ← zpow_mul, ← hn, hj]
    congr 1
    push_cast
    ring
  obtain ⟨z, hz_mem, hz_ord, hz_d, hz_P⟩ : ∃ z : X, z ∈ P ∧ orderOf z = 3 ^ v ∧
      z ^ 3 ^ (v - 1) = d ∧ Subgroup.zpowers z = P :=
    ⟨g0 ^ j, hzmem, hzord, hzd, hzP⟩
  have hφzmem : φ z ∈ Subgroup.zpowers z := by
    rw [hz_P]
    exact hPφ z hz_mem
  have hk_exists : ∃ k : ℕ, φ z = z ^ k := by
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hφzmem
    have hpos : (orderOf z : ℤ) ≠ 0 := by
      have := orderOf_pos z
      omega
    refine ⟨(m % (orderOf z : ℤ)).toNat, ?_⟩
    have hnn : (0 : ℤ) ≤ m % (orderOf z : ℤ) := Int.emod_nonneg _ hpos
    rw [← zpow_natCast, Int.toNat_of_nonneg hnn, zpow_mod_orderOf, hm]
  obtain ⟨k, hk⟩ := hk_exists
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    have hz1 : z = 1 := (MulEquiv.injective φ) (by rw [hk, map_one])
    rw [hz1, orderOf_one] at hz_ord
    have h9 : 9 ≤ 3 ^ v := by
      calc (9 : ℕ) = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ v := Nat.pow_le_pow_right (by norm_num) hv
    omega
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  have hpow : ∀ i : ℕ, φ (z ^ i) = z ^ (k * i) := by
    intro i
    rw [map_pow, hk, ← pow_mul]
  have hφ3' : ∀ x : X, φ (φ (φ x)) = x := by
    intro x
    have h1 : φ * (φ * φ) = 1 := by
      rw [← pow_three]
      exact hφ3
    have h2 := congrArg (fun ψ : MulAut X => ψ x) h1
    simpa [MulAut.mul_apply] using h2
  have hcube : z ^ (k * (k * k)) = z := by
    have h := hφ3' z
    rw [hk, hpow k, hpow (k * k)] at h
    exact h
  have hmodeq : k * (k * k) ≡ 1 [MOD orderOf z] := by
    apply pow_eq_pow_iff_modEq.mp
    rw [pow_one]
    exact hcube
  rw [hz_ord] at hmodeq
  have hle : 1 ≤ k * (k * k) := Nat.mul_pos hk1 (Nat.mul_pos hk1 hk1)
  have hdvd3 : 3 ^ v ∣ k * (k * k) - 1 := (Nat.modEq_iff_dvd' hle).mp hmodeq.symm
  have hdvd3' : 3 ^ v ∣ k ^ 3 - 1 := by
    rw [pow_three]
    exact hdvd3
  have hdiv : 3 ^ (v - 1) ∣ k - 1 := three_pow_sub_one_dvd_of_pow_three_eq_one_mod hv hk1 hdvd3'
  have hndiv : ¬ 3 ^ v ∣ k - 1 := by
    intro hdvd
    have hzk1 : z ^ (k - 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [hz_ord]; exact hdvd)
    have hφz : φ z = z := by
      rw [hk]
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [pow_succ, hzk1, one_mul]
    obtain ⟨y, hyP, hy⟩ := hmove
    apply hy
    have hyz : y ∈ Subgroup.zpowers z := by
      rw [hz_P]
      exact hyP
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hyz
    rw [← hm, map_zpow, hφz]
  exact ⟨z, k, hz_mem, hz_ord, hz_d, hk, hdiv, hndiv⟩

end CFSG.RankThree.PartTwo.Sec11

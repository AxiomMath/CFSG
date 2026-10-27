module

public import CFSG.Quasithin.Recognition.L34CIT.ParabolicInvolutions

public section

namespace CFSG.Quasithin.L34CIT

open Subgroup CFSG.Open

variable {A : Type} [Group A]

namespace Config

theorem eq_one_of_commute_of_orderOf_eq_three (C : Config A) {k t : A}
    (hk : orderOf k = 3) {n : ℕ} (ht : t ^ 2 ^ n = 1) (hc : t * k = k * t) : t = 1 := by
  by_contra ht1
  obtain ⟨a, ha⟩ := (exists_orderOf_eq_prime_pow_iff (p := 2)).mpr ⟨n, ht⟩
  have hapos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exfalso
      apply ht1
      rw [h, pow_zero] at ha
      exact orderOf_eq_one_iff.mp ha
    · exact h
  let e : A := t ^ 2 ^ (a - 1)
  have hsum : 2 ^ (a - 1) + 2 ^ (a - 1) = 2 ^ a := by
    have h1 : a - 1 + 1 = a := Nat.sub_add_cancel hapos
    calc 2 ^ (a - 1) + 2 ^ (a - 1) = 2 ^ (a - 1) * 2 := by ring
      _ = 2 ^ (a - 1 + 1) := by rw [pow_succ]
      _ = 2 ^ a := by rw [h1]
  have he2 : e * e = 1 := by
    have hsq : e * e = t ^ (2 ^ (a - 1) + 2 ^ (a - 1)) := by
      dsimp [e]
      rw [← pow_two, ← pow_mul]
      congr 1
      ring
    rw [hsq, hsum, ← ha]
    exact pow_orderOf_eq_one t
  have he1 : e ≠ 1 := by
    intro heq
    have heq' : t ^ 2 ^ (a - 1) = 1 := by simpa [e] using heq
    have hdvd : orderOf t ∣ 2 ^ (a - 1) := orderOf_dvd_of_pow_eq_one heq'
    rw [ha] at hdvd
    have hle : a ≤ a - 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
    omega
  have hce : e * k = k * e := by
    have hck : Commute t k := hc
    exact (hck.pow_left (2 ^ (a - 1))).eq
  have hkcent : k ∈ centralizer ({e} : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hce
  have hP2 : IsPGroup 2 (centralizer ({e} : Set A)) := C.isPGroup_centralizer e he2 he1
  obtain ⟨m, hm⟩ := hP2.exists_orderOf_eq_pow (⟨k, hkcent⟩ : centralizer ({e} : Set A))
  have hkord : orderOf (⟨k, hkcent⟩ : centralizer ({e} : Set A)) = 3 := by
    rw [Subgroup.orderOf_mk, hk]
  rw [hkord] at hm
  have h3dvd : 3 ∣ 2 ^ m := by rw [← hm]
  have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3dvd
  norm_num at h32

theorem exists_orderOf_eq_three (C : Config A) [Finite A] :
    ∃ k ∈ normalizer (C.T : Set A), orderOf k = 3 := by
  have hdvd : 3 ∣ Nat.card (normalizer (C.T : Set A)) := by
    rw [C.card_normalizer_T]
    norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨(x : A), x.2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact hx

theorem normalizer_zpowers_inf_normalizer_T (C : Config A) [Finite A] {k : A}
    (hkB : k ∈ normalizer (C.T : Set A)) (hk : orderOf k = 3) :
    normalizer (Subgroup.zpowers k : Set A) ⊓ normalizer (C.T : Set A) = Subgroup.zpowers k := by
  let N := normalizer (Subgroup.zpowers k : Set A) ⊓ normalizer (C.T : Set A)
  have hzle : Subgroup.zpowers k ≤ N :=
    le_inf Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hkB)
  have hzcard : Nat.card (Subgroup.zpowers k) = 3 := by
    rw [Nat.card_zpowers, hk]
  have hNT : N ⊓ (C.T : Subgroup A) = ⊥ := by
    rw [eq_bot_iff_forall]
    intro t ht
    obtain ⟨⟨htN, -⟩, htT⟩ := ht
    have hTz : (C.T : Subgroup A) ⊓ Subgroup.zpowers k = ⊥ := by
      rw [eq_bot_iff_forall]
      intro x hx
      obtain ⟨m, hm⟩ := C.T.isPGroup'.exists_pow_pow_eq_one ⟨x, hx.1⟩
      have hm' : x ^ 2 ^ m = 1 := by simpa using hm
      have hcomm : x * k = k * x := by
        obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx.2
        exact (Commute.refl k).zpow_left z |>.eq
      have hx1 : x = 1 := C.eq_one_of_commute_of_orderOf_eq_three hk hm' hcomm
      simpa using hx1
    have hcommT : t * k * t⁻¹ * k⁻¹ ∈ (C.T : Subgroup A) := by
      have hkt : k * t⁻¹ * k⁻¹ ∈ (C.T : Subgroup A) :=
        (Subgroup.mem_normalizer_iff.mp hkB t⁻¹).mp ((C.T : Subgroup A).inv_mem htT)
      have h := (C.T : Subgroup A).mul_mem htT hkt
      simpa [mul_assoc] using h
    have hcommZ : t * k * t⁻¹ * k⁻¹ ∈ Subgroup.zpowers k := by
      have hconj : t * k * t⁻¹ ∈ Subgroup.zpowers k :=
        (Subgroup.mem_normalizer_iff.mp htN k).mp (Subgroup.mem_zpowers k)
      have h := (Subgroup.zpowers k).mul_mem hconj
        ((Subgroup.zpowers k).inv_mem (Subgroup.mem_zpowers k))
      simpa [mul_assoc] using h
    have hbot : t * k * t⁻¹ * k⁻¹ ∈ (⊥ : Subgroup A) := by
      rw [← hTz]
      exact ⟨hcommT, hcommZ⟩
    have hcomm : t * k = k * t := by
      have h1 : t * k * t⁻¹ * k⁻¹ = 1 := by simpa using hbot
      calc t * k = (t * k * t⁻¹ * k⁻¹) * (k * t) := by group
        _ = 1 * (k * t) := by rw [h1]
        _ = k * t := by rw [one_mul]
    obtain ⟨m, hm⟩ := C.T.isPGroup'.exists_pow_pow_eq_one ⟨t, htT⟩
    exact C.eq_one_of_commute_of_orderOf_eq_three hk (by simpa using hm) hcomm
  have hodd : Odd (Nat.card ↥N) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    have h2 : 2 ∣ Nat.card ↥N := even_iff_two_dvd.mp heven
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hxpow : (x : A) ^ 2 ^ 1 = 1 := by
      rw [pow_one]
      have hxord : orderOf (x : A) = 2 := by rw [Subgroup.orderOf_coe, hx]
      simpa [hxord] using pow_orderOf_eq_one (x : A)
    have hxT : (x : A) ∈ (C.T : Subgroup A) :=
      mem_of_mem_normalizer_of_pow_eq_one (P := C.T) hxpow x.2.2
    have hxbot : (x : A) ∈ (⊥ : Subgroup A) := by
      rw [← hNT]
      exact ⟨x.2, hxT⟩
    have hx1 : (x : A) = 1 := by simpa using hxbot
    have hxord1 : orderOf x = 1 := by
      rw [← Subgroup.orderOf_coe, hx1, orderOf_one]
    rw [hx] at hxord1
    norm_num at hxord1
  have hdiv : Nat.card ↥N ∣ 192 := by
    have h := Subgroup.card_dvd_of_le (show N ≤ normalizer (C.T : Set A) from inf_le_right)
    rwa [C.card_normalizer_T] at h
  have hdiv3 : Nat.card ↥N ∣ 3 := by
    have hcop : Nat.Coprime (Nat.card ↥N) (2 ^ 6) := by
      rw [Nat.coprime_pow_right_iff (by norm_num)]
      exact hodd.coprime_two_right
    have h192 : (192 : ℕ) = 2 ^ 6 * 3 := by norm_num
    have hdvd' : Nat.card ↥N ∣ 2 ^ 6 * 3 := by
      rwa [h192] at hdiv
    exact hcop.dvd_of_dvd_mul_left hdvd'
  have hNcard : Nat.card ↥N = 3 := by
    have hge : 3 ≤ Nat.card ↥N := by
      rw [← hzcard]
      exact Subgroup.card_le_of_le hzle
    have hle : Nat.card ↥N ≤ 3 := Nat.le_of_dvd (by norm_num) hdiv3
    omega
  show N = Subgroup.zpowers k
  exact (Subgroup.eq_of_le_of_card_ge hzle (by rw [hzcard, hNcard])).symm

end Config

end CFSG.Quasithin.L34CIT

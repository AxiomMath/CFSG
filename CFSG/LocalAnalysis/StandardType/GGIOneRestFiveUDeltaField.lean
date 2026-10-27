module

public import Mathlib.FieldTheory.Finite.Extension

public section

namespace CFSG.StandardType.IOneUDelta

theorem pow_eq_zero_of_lt_two_mul {n b : ℕ} (hn : 1 ≤ n) (hb : b < 2 * n)
    (hb1 : (2 : ZMod (2 ^ n + 1)) ^ b = 1) : b = 0 := by
  have hneg : (2 : ZMod (2 ^ n + 1)) ^ n = -1 := by
    have h0 : ((2 ^ n + 1 : ℕ) : ZMod (2 ^ n + 1)) = 0 := ZMod.natCast_self _
    push_cast at h0
    linear_combination h0
  by_contra hne
  rcases lt_or_ge b n with hbn | hbn
  · have hlt : 2 ^ b < 2 ^ n + 1 := by
      have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hbn
      omega
    have hmod : 2 ^ b ≡ 1 [MOD 2 ^ n + 1] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      exact hb1
    have h1lt : 1 < 2 ^ n + 1 := by
      have := Nat.one_le_two_pow (n := n)
      omega
    rw [Nat.ModEq, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt h1lt] at hmod
    have hb0 : b = 0 := by
      have h2 : 2 ^ b = 2 ^ 0 := by simpa using hmod
      exact Nat.pow_right_injective (le_refl 2) h2
    exact hne hb0
  · obtain ⟨c, rfl⟩ : ∃ c, b = n + c := ⟨b - n, by omega⟩
    have hc : c < n := by omega
    rw [pow_add, hneg] at hb1
    have h0 : ((2 ^ c + 1 : ℕ) : ZMod (2 ^ n + 1)) = 0 := by
      push_cast
      linear_combination -hb1
    rw [ZMod.natCast_eq_zero_iff] at h0
    have hpos : 0 < 2 ^ c + 1 := Nat.succ_pos _
    have hle := Nat.le_of_dvd hpos h0
    have hlt : 2 ^ c < 2 ^ n := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hc
    omega

theorem two_mul_dvd_of_dvd_two_pow_sub_one {n i : ℕ} (hn : 1 ≤ n)
    (h : 2 ^ n + 1 ∣ 2 ^ i - 1) : 2 * n ∣ i := by
  have hneg : (2 : ZMod (2 ^ n + 1)) ^ n = -1 := by
    have h0 : ((2 ^ n + 1 : ℕ) : ZMod (2 ^ n + 1)) = 0 := ZMod.natCast_self _
    push_cast at h0
    linear_combination h0
  have h2n : (2 : ZMod (2 ^ n + 1)) ^ (2 * n) = 1 := by
    rw [mul_comm 2 n, pow_mul, hneg]
    norm_num
  have hi : (2 : ZMod (2 ^ n + 1)) ^ i = 1 := by
    have h0 : ((2 ^ i - 1 : ℕ) : ZMod (2 ^ n + 1)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr h
    have hpos : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    rw [Nat.cast_sub hpos] at h0
    push_cast at h0
    linear_combination h0
  have hsplit : (2 : ZMod (2 ^ n + 1)) ^ (i % (2 * n)) = 1 := by
    rw [← hi]
    conv_rhs => rw [← Nat.div_add_mod i (2 * n)]
    rw [pow_add, pow_mul, h2n, one_pow, one_mul]
  have hb : i % (2 * n) < 2 * n := Nat.mod_lt _ (by omega)
  exact Nat.dvd_of_mod_eq_zero (pow_eq_zero_of_lt_two_mul hn hb hsplit)

theorem sq_sub_one_eq_mul (Q : ℕ) (hQ : 1 ≤ Q) : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, Q = m + 1 := ⟨Q - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.sub_eq_of_eq_add (by ring : (m + 1) ^ 2 = m * (m + 1 + 1) + 1)]

theorem exists_orderOf_eq_succ {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) : ∃ ω : Kˣ, orderOf ω = 2 ^ n + 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hcard : Nat.card Kˣ = (2 ^ n) ^ 2 - 1 := by
    rw [Nat.card_units, hK]
  have hQ : 2 ≤ 2 ^ n := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn
    simpa using this
  have hdvd : 2 ^ n - 1 ∣ (2 ^ n) ^ 2 - 1 := by
    rw [sq_sub_one_eq_mul _ (by omega)]
    exact Dvd.intro _ rfl
  have hne : 2 ^ n - 1 ≠ 0 := by omega
  refine ⟨g ^ (2 ^ n - 1), ?_⟩
  rw [orderOf_pow' _ hne, hord, hcard, Nat.gcd_eq_right hdvd, sq_sub_one_eq_mul _ (by omega),
    Nat.mul_div_cancel_left _ (by omega)]

theorem fieldAut_eq_id_of_fix {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (τ : K ≃+* K)
    (hτ : ∀ x : K, x ^ (2 ^ n + 1) = 1 → τ x = x) : ∀ x : K, τ x = x := by
  letI : Algebra (ZMod 2) K := (ZMod.castHom (dvd_refl 2) K).toAlgebra
  have hcomm : ∀ x : ZMod 2, τ (algebraMap (ZMod 2) K x) = algebraMap (ZMod 2) K x := by
    intro x
    have h := RingHom.ext_zmod ((τ : K →+* K).comp (algebraMap (ZMod 2) K))
      (algebraMap (ZMod 2) K)
    exact congrArg (fun f : ZMod 2 →+* K => f x) h
  let g : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv (f := τ) hcomm
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 K g
  have hi' : ∀ x : K, τ x = x ^ 2 ^ i := by
    intro x
    have h := hi x
    simpa [g, ZMod.card] using h
  obtain ⟨ω, hω⟩ := exists_orderOf_eq_succ hn hK
  have hωK : (ω : K) ^ (2 ^ n + 1) = 1 := by
    have : ω ^ (2 ^ n + 1) = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
    have h2 := congrArg Units.val this
    simpa using h2
  have hfix := hτ (ω : K) hωK
  rw [hi'] at hfix
  have hpow : (ω : K) ^ (2 ^ i - 1) = 1 := by
    have hi1 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    have hω0 : (ω : K) ≠ 0 := ω.ne_zero
    have h3 : (ω : K) ^ (2 ^ i) = (ω : K) * (ω : K) ^ (2 ^ i - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h4 : (ω : K) * (ω : K) ^ (2 ^ i - 1) = (ω : K) * 1 := by
      rw [mul_one, ← h3, hfix]
    exact mul_left_cancel₀ hω0 h4
  have hpowU : ω ^ (2 ^ i - 1) = 1 := by
    apply Units.ext
    simpa using hpow
  have hdvd : 2 ^ n + 1 ∣ 2 ^ i - 1 := by
    rw [← hω]
    exact orderOf_dvd_of_pow_eq_one hpowU
  obtain ⟨m, hm⟩ := two_mul_dvd_of_dvd_two_pow_sub_one hn hdvd
  have hpc : ∀ y : K, y ^ Nat.card K = y := by
    intro y
    haveI := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card y
  have hpm : ∀ k : ℕ, ∀ y : K, y ^ (Nat.card K ^ k) = y := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ, pow_mul, ih y, hpc]
  have h2m : 2 ^ i = Nat.card K ^ m := by
    rw [hK, hm, ← pow_mul, ← pow_mul]
    congr 1
    ring
  intro x
  rw [hi' x, h2m]
  exact hpm m x

end CFSG.StandardType.IOneUDelta

end

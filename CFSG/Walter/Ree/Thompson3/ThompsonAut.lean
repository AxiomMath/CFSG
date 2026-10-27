module

public import CFSG.Walter.Ree.Thompson3.Invol
public import CFSG.Walter.Ree.Thompson2.Eq69
public import CFSG.Walter.Ree.Bombieri.Galois

public section

namespace CFSG.Walter.Ree.T2

variable {k : Type} [Field k] [CharP k 3] [Fintype k] {σ : k ≃+* k}

omit [CharP k 3] in
theorem pow_eq_pow_of_modEq' {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h : n ≡ m [MOD Fintype.card k - 1]) (x : k) : x ^ n = x ^ m := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_pow (by omega), zero_pow (by omega)]
  · have hu : (Units.mk0 x hx) ^ n = (Units.mk0 x hx) ^ m := by
      classical
      rw [pow_eq_pow_iff_modEq]
      refine h.of_dvd ?_
      rw [← Fintype.card_units]
      exact orderOf_dvd_card
    simpa using congrArg Units.val hu

theorem generates_nat {m : ℕ} (hk : Fintype.card k = 3 ^ m)
    (hgen : ∀ τ : k ≃+* k, ∃ j : ℤ, τ = σ ^ j) : ∀ τ : k ≃+* k, ∃ j : ℕ, τ = σ ^ j := by
  obtain ⟨b, -, hb⟩ := Bombieri.exists_eq_frob_pow hk σ
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · have := Fintype.one_lt_card (α := k); rw [hk] at this; simp at this
    · exact h
  have hfin : IsOfFinOrder σ := by
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, ?_⟩
    ext x
    rw [Bombieri.pow_apply_of_eq_frob_pow hb, RingAut.one_apply, mul_comm b m, pow_mul, ← hk,
      FiniteField.pow_card_pow]
  intro τ
  obtain ⟨j, hj⟩ := hgen τ
  have : τ ∈ Submonoid.powers σ := hfin.mem_powers_iff_mem_zpowers.mpr ⟨j, hj.symm⟩
  obtain ⟨n, hn⟩ := this
  exact ⟨n, hn.symm⟩

omit [CharP k 3] in
theorem exists_unit_orderOf {p : ℕ} (hp : p.Prime) (hpq : p ∣ Fintype.card k - 1) :
    ∃ w : kˣ, orderOf w = p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  apply exists_prime_orderOf_dvd_card
  rw [Fintype.card_units]; exact hpq

theorem sigmaQ_ker_of_gen {m : ℕ} (hk : Fintype.card k = 3 ^ m) (hm : Odd m)
    (hgen : ∀ τ : k ≃+* k, ∃ j : ℤ, τ = σ ^ j) : ∀ x : k, σ x * x = 1 → x = 1 ∨ x = -1 := by
  have hq : Fintype.card k % 4 = 3 := by
    obtain ⟨m', rfl⟩ := hm
    rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
  have hneg : ¬IsSquare (-1 : k) := by
    rw [FiniteField.isSquare_neg_one_iff, not_not]; exact hq
  intro x hx
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hσx : σ x = x⁻¹ := eq_inv_of_mul_eq_one_left hx
  have hσσ : σ (σ x) = x := by rw [hσx, map_inv₀, hσx, inv_inv]
  obtain ⟨j, hj⟩ := generates_nat hk hgen (frobeniusEquiv k 3)
  have h3 : x ^ 3 = (σ ^ j) x := by rw [← hj, frobeniusEquiv_def]
  have hpar : ∀ j : ℕ, (σ ^ j) x = x ∨ (σ ^ j) x = x⁻¹ := by
    intro j
    induction j with
    | zero => left; rfl
    | succ j ih =>
      rw [pow_succ', RingAut.mul_apply]
      rcases ih with h | h <;> rw [h]
      · right; exact hσx
      · left; rw [map_inv₀, hσx, inv_inv]
  have hx2 : x ^ 2 = 1 := by
    rcases hpar j with h | h <;> rw [h] at h3
    · have : x ^ 2 * x = 1 * x := by rw [← pow_succ, h3, one_mul]
      exact mul_right_cancel₀ hx0 this
    · have h4 : (x ^ 2) ^ 2 = 1 := by
        have : x ^ 3 * x = x⁻¹ * x := by rw [h3]
        rw [inv_mul_cancel₀ hx0, ← pow_succ] at this
        rw [← pow_mul]; exact this
      rcases sq_eq_one_iff.mp h4 with h5 | h5
      · exact h5
      · exact absurd ⟨x, by rw [← h5, sq]⟩ hneg
  rcases sq_eq_one_iff.mp hx2 with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem exists_a_of_ker {m : ℕ} (hk : Fintype.card k = 3 ^ m) (hm : Odd m) (hm3 : 3 ≤ m)
    (hker : ∀ x : k, σ x * x = 1 → x = 1 ∨ x = -1) :
    ∃ a : ℕ, Even a ∧ ∀ x : k, (σ x * x) ^ a = x ^ 2 := by
  classical
  obtain ⟨b, -, hb⟩ := Bombieri.exists_eq_frob_pow hk σ
  have hq : Fintype.card k % 4 = 3 := by
    obtain ⟨m', rfl⟩ := hm
    rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
  have hσ1 : ∀ x : k, σ x * x = x ^ (3 ^ b + 1) := fun x => by rw [hb, pow_succ]
  set q := Fintype.card k with hqdef
  have hq3 : 27 ≤ q := by
    rw [hk]; calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  obtain ⟨M, hM⟩ : ∃ M, q - 1 = 2 * M := ⟨(q - 1) / 2, by omega⟩
  have hModd : M % 2 = 1 := by omega
  obtain ⟨g, hg⟩ : ∃ g, 3 ^ b + 1 = 2 * g := by
    have : Odd (3 ^ b) := Odd.pow (by decide)
    obtain ⟨c, hc⟩ := this
    exact ⟨c + 1, by omega⟩
  have hcop : Nat.Coprime g M := by
    by_contra hc
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hc
    have hpg : p ∣ g := hpd.trans (Nat.gcd_dvd_left _ _)
    have hpM : p ∣ M := hpd.trans (Nat.gcd_dvd_right _ _)
    obtain ⟨w, hw⟩ := exists_unit_orderOf hp (by rw [hM]; exact hpM.mul_left 2)
    have hwg : w ^ g = 1 := orderOf_dvd_iff_pow_eq_one.mp (hw ▸ hpg)
    have hw1 : σ (w : k) * w = 1 := by
      rw [hσ1, hg, pow_mul', ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hwg]; simp
    have hp2 : p ∣ 2 := by
      rw [← hw]
      apply orderOf_dvd_of_pow_eq_one
      rcases hker _ hw1 with h | h
      · exact Units.ext (by simp [h])
      · exact Units.ext (by simp [h])
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
    subst this
    omega
  have hM1 : 1 < M := by omega
  obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hM1
  have hm'0 : m' ≠ 0 := by rintro rfl; simp at hm'
  have hmod : ∀ a : ℕ, g * a % M = 1 → (3 ^ b + 1) * a ≡ 2 [MOD q - 1] := by
    intro a ha
    have h1 : g * a ≡ 1 [MOD M] := by
      unfold Nat.ModEq; rw [ha, Nat.mod_eq_of_lt hM1]
    have h2 := h1.mul_left' 2
    rw [hM, hg, mul_assoc]
    simpa using h2
  by_cases hme : Even m'
  · refine ⟨m', hme, fun x => ?_⟩
    rw [hσ1, ← pow_mul]
    exact pow_eq_pow_of_modEq' (Nat.one_le_iff_ne_zero.mpr (by positivity)) (by norm_num)
      (hmod m' hm') x
  · refine ⟨m' + M, ?_, fun x => ?_⟩
    · rw [Nat.not_even_iff_odd] at hme
      obtain ⟨c, hc⟩ := hme
      exact ⟨c + M / 2 + 1, by omega⟩
    · rw [hσ1, ← pow_mul]
      have h1 := hmod m' hm'
      have h2 : (3 ^ b + 1) * (m' + M) ≡ 2 [MOD q - 1] := by
        have e : (3 ^ b + 1) * (m' + M) = (3 ^ b + 1) * m' + g * (q - 1) := by
          rw [hM, hg]; ring
        rw [e]
        unfold Nat.ModEq at h1 ⊢
        rw [Nat.add_mul_mod_self_right, h1]
      exact pow_eq_pow_of_modEq' (Nat.one_le_iff_ne_zero.mpr (by positivity)) (by norm_num) h2 x

theorem exists_a {m : ℕ} (hk : Fintype.card k = 3 ^ m) (hm : Odd m) (hm3 : 3 ≤ m)
    (hgen : ∀ τ : k ≃+* k, ∃ j : ℤ, τ = σ ^ j) :
    ∃ a : ℕ, Even a ∧ ∀ x : k, (σ x * x) ^ a = x ^ 2 :=
  exists_a_of_ker hk hm hm3 (sigmaQ_ker_of_gen hk hm hgen)

namespace RType

variable {d : k} {G : Type} [Group G] [Finite G] (R : RType G k σ d)

include R in
theorem exists_s
    {m : ℕ} (hk : Fintype.card k = 3 ^ m) :
    ∃ s : ℕ, Odd s ∧ ∀ x : k, (σ x * x ^ 2) ^ s = x := by
  classical
  obtain ⟨b, -, hb⟩ := Bombieri.exists_eq_frob_pow hk σ
  have hσ2 : ∀ x : k, σ x * x ^ 2 = x ^ (3 ^ b + 2) := fun x => by rw [hb, pow_add]
  have hm3 : 3 ≤ m := by
    have h := R.card_k
    rw [Nat.card_eq_fintype_card, hk] at h
    obtain ⟨n, hn, hqn⟩ := R.q_eq
    rw [hqn] at h
    have := Nat.pow_right_injective (show 2 ≤ 3 by norm_num) h
    omega
  set q := Fintype.card k with hqdef
  have hq27 : 27 ≤ q := by
    rw [hk]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  have hcop : Nat.Coprime (3 ^ b + 2) (q - 1) := by
    by_contra hc
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hc
    obtain ⟨w, hw⟩ := exists_unit_orderOf hp (hpd.trans (Nat.gcd_dvd_right _ _))
    have hwe : w ^ (3 ^ b + 2) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (hw ▸ hpd.trans (Nat.gcd_dvd_left _ _))
    have : w = 1 := R.sigmaTwo_injective (by
      rw [hσ2, ← Units.val_pow_eq_pow_val, hwe, Units.val_one])
    rw [this, orderOf_one] at hw
    exact hp.one_lt.ne hw
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  refine ⟨s, ?_, fun x => ?_⟩
  · have h2 : 2 ∣ q - 1 := by
      have : Odd q := by rw [hk]; exact Odd.pow (by decide)
      obtain ⟨c, hc⟩ := this
      exact ⟨c, by omega⟩
    have hodd : Odd ((3 ^ b + 2) * s) := by
      rw [Nat.odd_iff, ← Nat.mod_mod_of_dvd _ h2, hs]
    exact (Nat.odd_mul.mp hodd).2
  · rw [hσ2, ← pow_mul]
    have hmod : (3 ^ b + 2) * s ≡ 1 [MOD q - 1] := by
      unfold Nat.ModEq; rw [hs, Nat.mod_eq_of_lt (by omega)]
    rw [pow_eq_pow_of_modEq' (Nat.one_le_iff_ne_zero.mpr (by positivity)) le_rfl hmod x, pow_one]

include R in
theorem card_k_eq :
    ∃ n ≥ 1, Fintype.card k = 3 ^ (2 * n + 1) := by
  obtain ⟨n, hn, hq⟩ := R.q_eq
  exact ⟨n, hn, by rw [Fintype.card_eq_nat_card, R.card_k, hq]⟩

include R in
omit [Fintype k] in
theorem sigmaQ_ker : ∀ x : k, σ x * x = 1 → x = 1 ∨ x = -1 := by
  intro x hx
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have h1 := R.eq69_norm (Units.mk0 x hx0)
  have h2 := R.eq69_norm 1
  have e : ((Units.mk0 x hx0 : kˣ) : k) * σ ((Units.mk0 x hx0 : kˣ) : k) = 1 := by
    rw [Units.val_mk0, mul_comm, hx]
  have e1 : ((1 : kˣ) : k) * σ ((1 : kˣ) : k) = 1 := by simp
  rw [e] at h1
  rw [e1] at h2
  have h3 := mul_left_cancel (mul_right_cancel (mul_right_cancel (h1.trans h2.symm)))
  have h4 := R.ι_torus_injective h3
  simp only [inv_one, mul_one] at h4
  have h5 : Units.mk0 x hx0 * Units.mk0 x hx0 = 1 := by
    rw [← mul_inv_rev, inv_eq_one] at h4; exact h4
  rcases units_sq_eq_one h5 with h | h
  · left; simpa using congrArg Units.val h
  · right; simpa using congrArg Units.val h

include R in
theorem exists_a' :
    ∃ a : ℕ, Even a ∧ ∀ x : k, (σ x * x) ^ a = x ^ 2 := by
  obtain ⟨n, hn, hk⟩ := R.card_k_eq
  exact exists_a_of_ker hk (odd_two_mul_add_one n) (by omega) R.sigmaQ_ker

theorem isThompsonAut
    {m : ℕ} (hk : Fintype.card k = 3 ^ m) (hm : Odd m) (hm3 : 3 ≤ m)
    (hgen : ∀ τ : k ≃+* k, ∃ j : ℤ, τ = σ ^ j) (hT : ThompsonIdentity R) :
    IsThompsonAut k σ := by
  obtain ⟨a, ha, haσ⟩ := exists_a hk hm hm3 hgen
  obtain ⟨s, hs, hsσ⟩ := R.exists_s hk
  exact ⟨generates_nat hk hgen, a, s, ha, hs, haσ, hsσ, hT a ha haσ⟩

end RType

end CFSG.Walter.Ree.T2

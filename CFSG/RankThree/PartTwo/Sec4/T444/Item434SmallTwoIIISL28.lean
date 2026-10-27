module

public import CFSG.RankThree.PartTwo.KFacts.K71L28TwoFree

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

open CFSG CFSG.RankThree.PartTwo.KFacts
open Matrix
open scoped MatrixGroups Pointwise

section Trace

variable {K : Type*} [Field K]

theorem trace_sq_of_det_eq_one [CharP K 2] {M : Matrix (Fin 2) (Fin 2) K} (hM : M.det = 1) :
    (M ^ 2).trace = M.trace ^ 2 := by
  rw [mat2_sq_eq_trace_smul_add_one hM, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [Fintype.card_fin, smul_eq_mul, Nat.cast_ofNat, h2, add_zero, sq]

theorem coe_sl_mul (x r : SL(2, K)) :
    ((x * r : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      (x : Matrix (Fin 2) (Fin 2) K) * (r : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem coe_sl_one : ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 :=
  rfl

theorem coe_sl_pow (x : SL(2, K)) (n : ℕ) :
    ((x ^ n : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = (x : Matrix (Fin 2) (Fin 2) K) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, coe_sl_one]
  | succ n ih => rw [pow_succ, pow_succ, coe_sl_mul, ih]

theorem coe_sl_inv_mul (x : SL(2, K)) :
    ((x⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [← coe_sl_mul, inv_mul_cancel, coe_sl_one]

theorem sl_ext {x y : SL(2, K)}
    (h : (x : Matrix (Fin 2) (Fin 2) K) = (y : Matrix (Fin 2) (Fin 2) K)) : x = y :=
  Subtype.ext h

theorem trace_conj_sl2 (x r : SL(2, K)) :
    ((x * r * x⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).trace =
      ((r : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).trace := by
  rw [coe_sl_mul, coe_sl_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, coe_sl_inv_mul,
    Matrix.one_mul]

theorem eq_zero_or_one_of_pow_four (hK : Nat.card K = 8) {t : K} (ht : t ^ 4 = t) :
    t = 0 ∨ t = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have := Fintype.ofFinite K
  by_cases h0 : t = 0
  · exact Or.inl h0
  · right
    have h3 : t ^ 3 = 1 := by
      have h1 : t * (t ^ 3 - 1) = 0 := by linear_combination ht
      exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left h0)
    have h7 : t ^ 7 = 1 := by
      have h1 := FiniteField.pow_card_sub_one_eq_one t h0
      rwa [← Nat.card_eq_fintype_card, hK] at h1
    calc t = (t ^ 3) ^ 2 * t := by rw [h3, one_pow, one_mul]
      _ = t ^ 7 := by ring
      _ = 1 := h7

end Trace

section Seven

variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem card_sl2_eight (hK : Nat.card K = 8) : Nat.card SL(2, K) = 504 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  rw [CFSG.GorensteinWalter.sl2_card_formula, hK]
  norm_num

theorem sl28_eq_bot_of_normalizes_seven (hK : Nat.card K = 8) {x : SL(2, K)} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) {R : Subgroup SL(2, K)} (hR : IsPGroup 7 R)
    (hxR : ∀ y ∈ R, x * y * x⁻¹ ∈ R) : R = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcard := card_sl2_eight hK
  by_contra hne
  obtain ⟨⟨r, hrR⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  obtain ⟨m, hm⟩ := hR.exists_card_eq
  have hRdvd : 7 ^ m ∣ 504 := by rw [← hm, ← hcard]; exact Subgroup.card_subgroup_dvd_card R
  have hm1 : m ≤ 1 := by
    by_contra h
    have : 7 ^ 2 ∣ 504 := (pow_dvd_pow 7 (by omega)).trans hRdvd
    norm_num at this
  have hro : orderOf r ∣ 7 ^ m := by
    rw [← hm]
    exact Subgroup.orderOf_dvd_natCard R hrR
  have hor : orderOf r = 7 := by
    have h1 : orderOf r ∣ 7 := hro.trans (pow_dvd_pow 7 hm1 |>.trans (by norm_num))
    rcases (Nat.dvd_prime (by norm_num)).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hr1'
    · exact h
  have hRz : R = Subgroup.zpowers r := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hrR) ?_).symm
    rw [hm, Nat.card_zpowers, hor]
    calc 7 ^ m ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm1
      _ = 7 := by norm_num
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hRz ▸ hxR r hrR)
  set k := (j % 7).toNat with hk
  have hk7 : k < 7 := by omega
  have hrk : x * r * x⁻¹ = r ^ k := by
    rw [← hj, hk, ← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_mod_orderOf, hor]
    rfl
  have hpow : ∀ n : ℕ, x ^ n * r * (x ^ n)⁻¹ = r ^ (k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : x ^ (n + 1) * r * (x ^ (n + 1))⁻¹ = x * (x ^ n * r * (x ^ n)⁻¹) * x⁻¹ := by
        rw [pow_succ', _root_.mul_inv_rev]
        group
      rw [e, ih]
      have hc : ∀ t : ℕ, x * r ^ t * x⁻¹ = (x * r * x⁻¹) ^ t := fun t => by
        rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
      rw [hc, hrk, ← pow_mul, pow_succ, mul_comm]
  have hk3 : r ^ (k ^ 3) = r ^ 1 := by
    rw [← hpow 3, hx3, one_mul, inv_one, mul_one, pow_one]
  have hmod : k ^ 3 ≡ 1 [MOD 7] := by
    have := (pow_eq_pow_iff_modEq).mp hk3
    rwa [hor] at this
  have hcases : k = 1 ∨ k = 2 ∨ k = 4 := by
    clear_value k
    interval_cases k <;> revert hmod <;> decide
  have hdx : ((x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).det = 1 := x.2
  have hdr : ((r : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).det = 1 := r.2
  have hr7 : r ^ 7 = 1 := by rw [← hor]; exact pow_orderOf_eq_one r
  have hr6 : r ^ 6 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hor] at this
    norm_num at this
  have htr : ((x * r * x⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).trace =
      ((r : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).trace := trace_conj_sl2 x r
  have hsq : ((r ^ 2 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).trace =
      ((r : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).trace ^ 2 := by
    rw [coe_sl_pow]
    exact trace_sq_of_det_eq_one hdr
  have hsq4 : ((r ^ 4 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).trace =
      ((r : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).trace ^ 4 := by
    have e : r ^ 4 = (r ^ 2) ^ 2 := by rw [← pow_mul]
    rw [e, coe_sl_pow, trace_sq_of_det_eq_one (r ^ 2).2, hsq, ← pow_mul]
  have hsix : ∀ t : SL(2, K), ((t : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).trace = 0 ∨
      ((t : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).trace = 1 → t ^ 6 = 1 := fun t ht =>
    sl_ext (by rw [coe_sl_pow, coe_sl_one]; exact mat2_pow_six_eq_one_of_trace t.2 ht)
  rcases hcases with h1 | h2 | h4
  ·
    rw [h1, pow_one] at hrk
    have hcomm : ((r : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * x = x * r := by
      have e : x * r = r * x := by
        calc x * r = x * r * x⁻¹ * x := by group
          _ = r * x := by rw [hrk]
      rw [← coe_sl_mul, ← coe_sl_mul, e]
    have hx3' : ((x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1 := by
      rw [← coe_sl_pow, hx3, coe_sl_one]
    have hx1' : ((x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ≠ 1 := fun h =>
      hx1 (sl_ext (by rw [h, coe_sl_one]))
    have h9 := mat2_pow_nine_eq_one_of_commute hK hdx hx3' hx1' hdr hcomm
    have h9' : r ^ 9 = 1 := sl_ext (by rw [coe_sl_pow, h9, coe_sl_one])
    have := orderOf_dvd_of_pow_eq_one h9'
    rw [hor] at this
    norm_num at this
  ·
    rw [h2] at hrk
    rw [hrk, hsq] at htr
    have h01 : ((r : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).trace = 0 ∨
        ((r : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).trace = 1 := by
      have h1 : ((r : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).trace *
          (((r : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).trace - 1) = 0 := by
        linear_combination htr
      rcases mul_eq_zero.mp h1 with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    exact hr6 (hsix r h01)
  ·
    rw [h4] at hrk
    rw [hrk, hsq4] at htr
    exact hr6 (hsix r (eq_zero_or_one_of_pow_four hK htr))

end Seven

theorem sl28_eq_bot_of_normalizes_two {x : SL(2, GaloisField 2 3)} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) {R : Subgroup SL(2, GaloisField 2 3)} (hR : IsPGroup 2 R)
    (hxR : ∀ y ∈ R, x * y * x⁻¹ ∈ R) : R = ⊥ := by
  set ψ := CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 3)
  have h := psl28_eq_bot_of_normalizes (x := ψ.symm x)
    (by rw [← map_pow, hx3, map_one]) (ψ.symm.map_ne_one_iff.mpr hx1)
    (X := R.map (ψ.symm : SL(2, GaloisField 2 3) →* PSL(2, GaloisField 2 3)))
    (hR.map _) (by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨x * y * x⁻¹, hxR y hy, ?_⟩
      change ψ.symm (x * y * x⁻¹) = ψ.symm x * ψ.symm y * (ψ.symm x)⁻¹
      rw [map_mul, map_mul, map_inv])
  rw [Subgroup.map_eq_bot_iff_of_injective _ ψ.symm.injective] at h
  exact h

theorem exists_sylow_invariant {W : Type*} [Group W] [Finite W] {r : ℕ} [Fact r.Prime]
    (φ : MulAut W) (hφ : φ ^ 3 = 1) (h3 : ¬ 3 ∣ Nat.card (Sylow r W)) :
    ∃ P : Sylow r W, ∀ y ∈ (P : Subgroup W), φ y ∈ (P : Subgroup W) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Subgroup.zpowers φ with hH
  have hHp : IsPGroup 3 H := by
    intro h
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.2
    rw [Subgroup.coe_pow, pow_one, ← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul,
      zpow_natCast, hφ, _root_.one_zpow, Subgroup.coe_one]
  obtain ⟨P, hP⟩ := hHp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow r W) h3
  refine ⟨P, fun y hy => ?_⟩
  have hPφ : (⟨φ, Subgroup.mem_zpowers φ⟩ : H) • P = P := hP _
  have h1 : φ y ∈ ((⟨φ, Subgroup.mem_zpowers φ⟩ : H) • P : Sylow r W) :=
    Subgroup.smul_mem_pointwise_smul y φ (P : Subgroup W) hy
  rwa [hPφ] at h1

theorem divisors_fiftySix : ∀ n : ℕ, n ∣ 56 →
    (n % 2 = 1 → ¬ 3 ∣ n) ∧ (n % 7 = 1 → ¬ 3 ∣ n) ∧ (¬ 2 ∣ n → ¬ 7 ∣ n → n = 1) := by
  intro n hn
  have hle : n ≤ 56 := Nat.le_of_dvd (by norm_num) hn
  interval_cases n <;> simp_all

theorem sl28_eq_bot_of_normalizes_coprime {x : SL(2, GaloisField 2 3)} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) {W : Subgroup SL(2, GaloisField 2 3)} (hW : ¬ 3 ∣ Nat.card W)
    (hxW : ∀ y ∈ W, x * y * x⁻¹ ∈ W) : W = ⊥ := by
  have hK : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  have hcard := card_sl2_eight hK
  have hx2 : ∀ y, x * y * x⁻¹ ∈ W → y ∈ W := by
    intro y hy
    have h1 := hxW _ (hxW _ hy)
    have hx3' : x * x * x = 1 := by
      rw [pow_succ, pow_two] at hx3
      exact hx3
    have e : x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * y * (x * x * x)⁻¹ := by group
    rwa [e, hx3', one_mul, inv_one, mul_one] at h1
  have hxN : x ∈ Subgroup.normalizer (W : Set SL(2, GaloisField 2 3)) :=
    Subgroup.mem_normalizer_iff.mpr fun y => ⟨hxW y, hx2 y⟩
  set φ : MulAut W := W.normalizerMonoidHom ⟨x, hxN⟩ with hφdef
  have hφy : ∀ y : W, ((φ y : W) : SL(2, GaloisField 2 3)) = x * y * x⁻¹ := fun y => rfl
  have hφ3 : φ ^ 3 = 1 := by
    rw [hφdef, ← map_pow]
    have : (⟨x, hxN⟩ : Subgroup.normalizer (W : Set SL(2, GaloisField 2 3))) ^ 3 = 1 :=
      Subtype.ext (by simp [hx3])
    rw [this, map_one]
  have hW56 : Nat.card W ∣ 56 := by
    have h1 : Nat.card W ∣ 9 * 56 := by
      rw [show 9 * 56 = Nat.card SL(2, GaloisField 2 3) by rw [hcard]]
      exact Subgroup.card_subgroup_dvd_card W
    have hcop : Nat.Coprime (Nat.card W) 9 := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact Nat.Coprime.pow_right 2
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hW).symm
    exact hcop.dvd_of_dvd_mul_left h1
  have hsyl : ∀ (r : ℕ) [Fact r.Prime], (Nat.card (Sylow r W) % r = 1 → ¬ 3 ∣
      Nat.card (Sylow r W)) → ∃ P : Sylow r W, ∀ y ∈ (P : Subgroup W),
        φ y ∈ (P : Subgroup W) := by
    intro r _ h
    refine exists_sylow_invariant φ hφ3 (h ?_)
    have h1 := card_sylow_modEq_one r W
    unfold Nat.ModEq at h1
    rw [h1, Nat.one_mod_eq_one]
    exact (Fact.out : r.Prime).ne_one
  have hdvd : ∀ (r : ℕ) [Fact r.Prime], Nat.card (Sylow r W) ∣ 56 := by
    intro r _
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow r W))
    exact (P.card_dvd_index.trans (Subgroup.index_dvd_card _)).trans hW56
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hkill : ∀ (r : ℕ) [Fact r.Prime] (P : Sylow r W), (∀ y ∈ (P : Subgroup W),
      φ y ∈ (P : Subgroup W)) →
      ((P : Subgroup W).map W.subtype = ⊥ → ¬ r ∣ Nat.card W) := by
    intro r _ P _ hbot
    have hP1 : Nat.card (P : Subgroup W) = 1 := by
      rw [Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective] at hbot
      rw [hbot, Subgroup.card_bot]
    rw [P.card_eq_multiplicity] at hP1
    have hfac : (Nat.card W).factorization r = 0 := by
      rcases Nat.pow_eq_one.mp hP1 with h | h
      · exact absurd h (Fact.out : r.Prime).ne_one
      · exact h
    intro hr
    rw [Nat.factorization_eq_zero_iff] at hfac
    rcases hfac with h | h | h
    · exact h Fact.out
    · exact h hr
    · exact Nat.card_pos.ne' h
  obtain ⟨P2, hP2⟩ := hsyl 2 ((divisors_fiftySix _ (hdvd 2)).1)
  obtain ⟨P7, hP7⟩ := hsyl 7 ((divisors_fiftySix _ (hdvd 7)).2.1)
  have hinv : ∀ (r : ℕ) [Fact r.Prime] (P : Sylow r W), (∀ y ∈ (P : Subgroup W),
      φ y ∈ (P : Subgroup W)) → ∀ y ∈ (P : Subgroup W).map W.subtype,
        x * y * x⁻¹ ∈ (P : Subgroup W).map W.subtype := by
    rintro r _ P hP _ ⟨y, hy, rfl⟩
    exact ⟨φ y, hP y hy, hφy y⟩
  have h2 : ¬ 2 ∣ Nat.card W := hkill 2 P2 hP2 (sl28_eq_bot_of_normalizes_two hx3 hx1
    (P2.isPGroup'.map _) (hinv 2 P2 hP2))
  have h7 : ¬ 7 ∣ Nat.card W := hkill 7 P7 hP7 (sl28_eq_bot_of_normalizes_seven hK hx3 hx1
    (P7.isPGroup'.map _) (hinv 7 P7 hP7))
  exact Subgroup.card_eq_one.mp ((divisors_fiftySix _ hW56).2.2 h2 h7)

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

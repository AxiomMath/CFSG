module

public import CFSG.Walter.Ree.Bombieri.Appendix
import CFSG.Walter.Ree.Bombieri.Galois

public section

namespace CFSG.Walter.Ree.Bombieri

open Polynomial

@[expose] def ArithFacts (k b s a : ℕ) : Prop :=
  (3 ^ b + 2) * s % (3 ^ k - 1) = 1 ∧ (3 ^ b + 1) * a % (3 ^ k - 1) = 2 ∧ a % 2 = 0 ∧
    (3 ^ k - 1) % 2 = 0 ∧ (3 ^ k - 1) / 2 % 2 = 1 ∧ (3 ^ b + 1) % 2 = 0 ∧
    Nat.gcd ((3 ^ b + 1) / 2) ((3 ^ k - 1) / 2) = 1

@[expose] noncomputable def oddU (b s : ℕ) : (ZMod 3)[X] :=
  ((X + 1) ^ s) ^ (3 ^ b + 1) - ((X - 1) ^ s) ^ (3 ^ b + 1)

@[expose] noncomputable def oddT (b s a : ℕ) : (ZMod 3)[X] :=
  (X + 1) ^ s * (oddU b s - 1) ^ a - ((X + 1) ^ s - (X - 1) ^ s + 1) * oddU b s ^ a -
    (X - 1) ^ s * (oddU b s + 1) ^ a + (oddU b s - 1) ^ a * (oddU b s + 1) ^ a

@[expose] def CaseFacts (f : (ZMod 3)[X]) (k b : ℕ) : Prop :=
  ∃ s a : ℕ, ArithFacts k b s a ∧ ∃ w : (ZMod 3)[X],
    f ∣ oddU b s * (oddU b s - 1) * (oddU b s + 1) * oddT b s a * w - 1

@[expose] def Skip (k b : ℕ) : Prop :=
  Nat.gcd b k ≠ 1 ∨ 2 * b % k = 1 ∨ Nat.gcd (3 ^ b + 2) (3 ^ k - 1) ≠ 1

@[expose] def AppOK (k : ℕ) : Prop :=
  ∃ f : (ZMod 3)[X], f.coeff k ≠ 0 ∧ f ∣ X ^ 3 ^ k - X ∧ ∀ b < k, Skip k b ∨ CaseFacts f k b

variable {K : Type*} [Field K] [Fintype K] [CharP K 3]

theorem exists_root_of_dvd {k : ℕ} (hk : 1 ≤ k) (hK : Fintype.card K = 3 ^ k)
    {f : (ZMod 3)[X]} (hc : f.coeff k ≠ 0) (hdvd : f ∣ X ^ 3 ^ k - X) :
    ∃ r : K, f.eval₂ (castThree K) r = 0 := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hsplit : Splits (X ^ Fintype.card K - X : K[X]) := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq K hq]
    rfl
  have hdvdK : f.map (castThree K) ∣ X ^ Fintype.card K - X := by
    rw [hK]
    simpa using Polynomial.map_dvd (castThree K) hdvd
  have hgs := hsplit.of_dvd (FiniteField.X_pow_card_sub_X_ne_zero K hq) hdvdK
  have hcoeff : (f.map (castThree K)).coeff k ≠ 0 := by
    rw [coeff_map]
    exact (map_ne_zero_iff _ (castThree K).injective).mpr hc
  have hdeg : (f.map (castThree K)).degree ≠ 0 := by
    have hne : f.map (castThree K) ≠ 0 := fun h0 => hcoeff (by rw [h0, coeff_zero])
    rw [degree_eq_natDegree hne]
    have := le_natDegree_of_ne_zero hcoeff
    exact_mod_cast (by omega : (f.map (castThree K)).natDegree ≠ 0)
  obtain ⟨r, hr⟩ := hgs.exists_eval_eq_zero hdeg
  exact ⟨r, by rwa [eval_map] at hr⟩

theorem caseFacts_sound {k b : ℕ} (hK : Fintype.card K = 3 ^ k) {f : (ZMod 3)[X]} {r : K}
    (hr : f.eval₂ (castThree K) r = 0) (h : CaseFacts f k b) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 3 ^ b) {a : ℕ} (ha : Even a) (hB : ∀ x : K, (σ x * x) ^ a = x ^ 2) :
    ∃ p ∈ ESigma K σ, thompsonT a p.1 p.2.1 p.2.2 ≠ 0 := by
  obtain ⟨s, ac, ⟨hs, hac, haeven, hq2, hhodd, hb2, hgcd⟩, w, hdvd⟩ := h
  rw [← hK] at hs hac hq2 hhodd hgcd
  set ι := castThree K
  have hev : ∀ g : (ZMod 3)[X], f ∣ g → g.eval₂ ι r = 0 := by
    rintro g ⟨c, rfl⟩
    rw [eval₂_mul, hr, zero_mul]
  set z : K := (r + 1) ^ s with hz
  set y : K := (r - 1) ^ s with hy
  set u : K := z ^ (3 ^ b + 1) - y ^ (3 ^ b + 1) with hu
  have eU : (oddU b s).eval₂ ι r = u := by
    simp only [oddU, eval₂_sub, eval₂_pow, eval₂_add, eval₂_X, eval₂_one, hu, hz, hy]
  have eT : (oddT b s ac).eval₂ ι r = z * (u - 1) ^ ac - (z - y + 1) * u ^ ac -
      y * (u + 1) ^ ac + (u - 1) ^ ac * (u + 1) ^ ac := by
    simp only [oddT, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_add, eval₂_X, eval₂_one, eU, hz, hy]
  have h1 := hev _ hdvd
  simp only [eval₂_sub, eval₂_mul, eval₂_add, eval₂_one, eU, eT] at h1
  have hprod : u * (u - 1) * (u + 1) *
      (z * (u - 1) ^ ac - (z - y + 1) * u ^ ac - y * (u + 1) ^ ac + (u - 1) ^ ac * (u + 1) ^ ac) *
        w.eval₂ ι r = 1 := by
    rw [← sub_eq_zero]; exact h1
  have hne := fun (h0 : u * (u - 1) * (u + 1) *
      (z * (u - 1) ^ ac - (z - y + 1) * u ^ ac - y * (u + 1) ^ ac + (u - 1) ^ ac * (u + 1) ^ ac)
      = 0) => by rw [h0, zero_mul] at hprod; exact zero_ne_one hprod
  have nT : z * (u - 1) ^ ac - (z - y + 1) * u ^ ac - y * (u + 1) ^ ac +
      (u - 1) ^ ac * (u + 1) ^ ac ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
  have nu0 : u ≠ 0 := fun h0 => hne (by rw [h0]; ring)
  have nu1 : u - 1 ≠ 0 := fun h0 => hne (by rw [h0]; ring)
  have nu2 : u + 1 ≠ 0 := fun h0 => hne (by rw [h0]; ring)
  have hpow (v : K) : (v ^ s) ^ (3 ^ b + 2) = v := by
    rw [← pow_mul, mul_comm]; exact pow_eq_self_of_mod hs v
  have hq1 : 2 < Fintype.card K - 1 := by
    have hpos : 0 < Fintype.card K - 1 := by have := Fintype.one_lt_card (α := K); omega
    have := Nat.mod_lt ((3 ^ b + 1) * ac) hpos
    omega
  have hmodA : a ≡ ac [MOD Fintype.card K - 1] := by
    have h1 := modEq_of_exponent hσ hB
    have h2 : (3 ^ b + 1) * ac ≡ 2 [MOD Fintype.card K - 1] := by
      unfold Nat.ModEq; rw [hac, Nat.mod_eq_of_lt hq1]
    have h12 := h1.trans h2.symm
    obtain ⟨c, hc⟩ : ∃ c, 3 ^ b + 1 = 2 * c := ⟨(3 ^ b + 1) / 2, by omega⟩
    obtain ⟨hh, hh'⟩ : ∃ hh, Fintype.card K - 1 = 2 * hh := ⟨(Fintype.card K - 1) / 2, by omega⟩
    rw [hc, hh', mul_assoc, mul_assoc] at h12
    have h3 := Nat.ModEq.mul_left_cancel' two_ne_zero h12
    rw [show (3 ^ b + 1) / 2 = c by omega, show (Fintype.card K - 1) / 2 = hh by omega] at hgcd
    have h4 : a ≡ ac [MOD hh] :=
      Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hgcd) h3
    have h5 : a ≡ ac [MOD 2] := by
      unfold Nat.ModEq; rw [Nat.even_iff.mp ha, haeven]
    have hodd : Odd hh := Nat.odd_iff.mpr (by
      rw [show (Fintype.card K - 1) / 2 = hh by omega] at hhodd; exact hhodd)
    rw [hh']
    exact (Nat.modEq_and_modEq_iff_modEq_mul (Nat.coprime_two_left.mpr hodd)).mp ⟨h5, h4⟩
  refine ⟨(z, y, u), ⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [hσ]
    rw [← pow_add, ← pow_add, hz, hy, hpow, hpow]
    linear_combination (three_eq_zero (K := K))
  · simp only [hσ]
    rw [← pow_succ, ← pow_succ]
  · intro h3
    have : (u - 1) * u * (u + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact nu1 h
      · exact nu0 h
    · exact nu2 h
  · simp only [thompsonT]
    rw [pow_eq_pow_of_modEq hmodA nu1, pow_eq_pow_of_modEq hmodA nu0,
      pow_eq_pow_of_modEq hmodA nu2,
      show u ^ 2 - 1 = (u - 1) * (u + 1) by ring,
      pow_eq_pow_of_modEq hmodA (mul_ne_zero nu1 nu2), mul_pow]
    exact nT

theorem sq_eq_frob_of_appOK {k : ℕ} (hk : 2 ≤ k) (hK : Fintype.card K = 3 ^ k) (h : AppOK k)
    {σ : K ≃+* K} (hσ : IsThompsonAut K σ) : ∀ x, σ (σ x) = x ^ 3 := by
  obtain ⟨f, hc, hdvd, hall⟩ := h
  obtain ⟨hA, a, s, ha, -, hB1, hB2, hC⟩ := hσ
  obtain ⟨b, hbk, hb⟩ := exists_eq_frob_pow hK σ
  have hcop : Nat.Coprime b k := coprime_of_generates hK hk hb hA
  by_cases h2b : 2 * b % k = 1
  · intro x
    rw [hb, hb, ← pow_mul, ← pow_add, ← two_mul, pow_three_pow_mod hK, h2b, pow_one]
  · have hgcd : Nat.Coprime (3 ^ b + 2) (3 ^ k - 1) :=
      coprime_of_bijective_pow hK (s := s) fun x => by
        have := hB2 x; rwa [hb, ← pow_add] at this
    have hcase : CaseFacts f k b := by
      rcases hall b hbk with (h | h | h) | h
      · exact absurd hcop h
      · exact absurd h h2b
      · exact absurd hgcd h
      · exact h
    obtain ⟨r, hr⟩ := exists_root_of_dvd (by omega) hK hc hdvd
    obtain ⟨p, hp, hT⟩ := caseFacts_sound hK hr hcase hb ha hB1
    exact absurd (hC p hp) hT

theorem sq_eq_frob_of_appRange {lo hi : ℕ}
    (hc : ∀ k, lo ≤ k → k ≤ hi → k % 2 = 1 → AppOK k) {k : ℕ} (hk : 3 ≤ k) (hodd : k % 2 = 1)
    (hlo : lo ≤ k) (hhi : k ≤ hi) (hK : Fintype.card K = 3 ^ k) {σ : K ≃+* K}
    (hσ : IsThompsonAut K σ) : ∀ x, σ (σ x) = x ^ 3 :=
  sq_eq_frob_of_appOK (by omega) hK (hc k hlo hhi hodd) hσ

end CFSG.Walter.Ree.Bombieri

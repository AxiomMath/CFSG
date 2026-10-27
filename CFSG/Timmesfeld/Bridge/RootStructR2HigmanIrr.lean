module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDescent
public import Mathlib.Data.Int.Star

public section

namespace CFSG.Timmesfeld.Bridge.Higman

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

theorem le_card_mul_gcd_of_shift {n d : ℕ} (hn : 0 < n) {J : Finset ℕ} (hJne : J.Nonempty)
    (hJn : ∀ i ∈ J, i < n) (hshift : J.image (fun i => (i + d) % n) = J) :
    n ≤ J.card * Nat.gcd n d := by
  obtain ⟨i₀, hi₀⟩ := hJne
  set g := Nat.gcd n d with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left d hn
  have hgn : g ∣ n := Nat.gcd_dvd_left n d
  set f : ℕ → ℕ := fun j => (i₀ + j * d) % n with hf
  have hfJ : ∀ j, f j ∈ J := by
    intro j
    induction j with
    | zero =>
      simp only [hf, zero_mul, add_zero]
      rw [Nat.mod_eq_of_lt (hJn i₀ hi₀)]
      exact hi₀
    | succ j ih =>
      have h1 : (f j + d) % n ∈ J := by
        rw [← hshift]
        exact Finset.mem_image_of_mem _ ih
      have h2 : f (j + 1) = (f j + d) % n := by
        simp only [hf]
        rw [show i₀ + (j + 1) * d = i₀ + j * d + d by ring, Nat.add_mod (i₀ + j * d) d n,
          Nat.add_mod ((i₀ + j * d) % n) d n, Nat.mod_mod]
      rw [h2]
      exact h1
  have hinj : Set.InjOn f (Finset.range (n / g) : Set ℕ) := by
    intro j hj j' hj' he
    simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
    have h1 : i₀ + j * d ≡ i₀ + j' * d [MOD n] := he
    have h2 : j * d ≡ j' * d [MOD n] := Nat.ModEq.add_left_cancel' i₀ h1
    have h3 := Nat.ModEq.cancel_right_div_gcd hn h2
    exact Nat.ModEq.eq_of_lt_of_lt h3 hj hj'
  have hcard : (Finset.range (n / g)).card ≤ J.card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card (fun x hx => by
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
      exact hfJ j)
  rw [Finset.card_range] at hcard
  calc n = n / g * g := (Nat.div_mul_cancel hgn).symm
    _ ≤ J.card * g := Nat.mul_le_mul_right g hcard

theorem five_mul_le_two_mul_two_pow {k : ℕ} (hk : 3 ≤ k) : 5 * k ≤ 2 * 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

theorem mul_two_pow_eq {n d k : ℕ} (hn : 0 < n) (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hkg : n ≤ k * Nat.gcd n d) (hlt : 2 * d * 2 ^ k < 5 * n) : d * 2 ^ k = 2 * n := by
  set g := Nat.gcd n d with hg
  have hgd : g ≤ d := Nat.le_of_dvd hd (Nat.gcd_dvd_right n d)
  have hgn : g ∣ n := Nat.gcd_dvd_left n d
  have hgd' : g ∣ d := Nat.gcd_dvd_right n d
  have hgle : g ≤ n := Nat.le_of_dvd hn hgn
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · interval_cases k
    ·
      have hgn' : g = n := le_antisymm hgle (by simpa using hkg)
      obtain ⟨t, ht⟩ := hgd'
      rw [hgn'] at ht
      have ht1 : t = 1 := by
        rcases Nat.lt_or_ge t 2 with h | h
        · rcases Nat.lt_or_ge t 1 with h' | h'
          · have : t = 0 := by omega
            subst this
            omega
          · omega
        · have : 2 * n ≤ n * t := by nlinarith
          rw [ht] at hlt
          nlinarith
      rw [ht, ht1]
      ring
    ·
      obtain ⟨m, hm⟩ := hgn
      obtain ⟨t, ht⟩ := hgd'
      have hg0 : 0 < g := Nat.gcd_pos_of_pos_left d hn
      have hm2 : m ≤ 2 := by
        rw [hm] at hkg
        nlinarith
      have ht1 : t = 1 := by
        rw [ht, hm] at hlt
        have : 1 ≤ t := by
          rcases Nat.eq_zero_or_pos t with h | h
          · subst h
            omega
          · exact h
        nlinarith
      have hm2' : m = 2 := by
        rcases Nat.lt_or_ge m 2 with h | h
        · rw [ht, ht1, hm] at hlt
          interval_cases m <;> omega
        · omega
      rw [ht, ht1, hm, hm2']
      ring
  ·
    exfalso
    have h1 : n ≤ k * d := hkg.trans (Nat.mul_le_mul_left k hgd)
    have h2 := five_mul_le_two_mul_two_pow hk3
    have h3 : 5 * n ≤ 2 * d * 2 ^ k := by
      calc 5 * n ≤ 5 * (k * d) := Nat.mul_le_mul_left 5 h1
        _ = (5 * k) * d := by ring
        _ ≤ (2 * 2 ^ k) * d := Nat.mul_le_mul_right d h2
        _ = 2 * d * 2 ^ k := by ring
    omega

set_option synthInstance.maxHeartbeats 400000 in
theorem card_eq_sq_of_irreducible {n : ℕ} (hn : 1 ≤ n) {F : Type*} [Field F] [Fintype F]
    [CharP F 2] (hF : Fintype.card F = 2 ^ n) {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) (hW : Nat.card W ^ 2 < (2 ^ n) ^ 5) : Nat.card W = (2 ^ n) ^ 2 := by
  classical
  obtain ⟨d, hd1, hDcard, hb⟩ := binary_SL2_irreducible_Frobenius_descent hn hF ρ hnt
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιF, ιD, J, hJne, hJn, -, hshift, hdim⟩ :=
    hb (Module.finBasis (EndRing ρ) W)
  have hWcard : Nat.card W = 2 ^ (d * 2 ^ J.card) := by
    rw [Module.natCard_eq_pow_finrank (K := EndRing ρ) (V := W), hDcard, hdim, ← pow_mul]
  have hkg := le_card_mul_gcd_of_shift (by omega) hJne hJn hshift
  have hk : 1 ≤ J.card := Finset.card_pos.mpr hJne
  have hlt : 2 * d * 2 ^ J.card < 5 * n := by
    rw [hWcard, ← pow_mul, ← pow_mul] at hW
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hW
    linarith
  rw [hWcard, mul_two_pow_eq (by omega) hd1 hk hkg hlt, ← pow_mul, mul_comm]

end CFSG.Timmesfeld.Bridge.Higman

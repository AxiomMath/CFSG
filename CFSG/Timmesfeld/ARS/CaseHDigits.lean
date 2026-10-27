module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Timmesfeld.ARS.CaseH

@[expose] def geom (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 1 + q * geom q k

theorem geom_succ (q k : ℕ) : geom q (k + 1) = 1 + q * geom q k := rfl

theorem geom_one (q : ℕ) : geom q 1 = 1 := by simp [geom]

theorem geom_mul (q k : ℕ) (hq : 1 ≤ q) : geom q k * (q - 1) = q ^ k - 1 := by
  induction k with
  | zero => simp [geom]
  | succ k ih =>
    rw [geom_succ, add_mul, one_mul, mul_assoc, ih]
    have h1 : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
    have h2 : 1 ≤ q ^ (k + 1) := Nat.one_le_pow _ _ hq
    zify [hq, h1, h2]
    ring

theorem geom_odd {q k : ℕ} (hq : q % 2 = 0) (hk : 1 ≤ k) : geom q k % 2 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [geom_succ]
  have : q * geom q k % 2 = 0 := by rw [Nat.mul_mod, hq, zero_mul, Nat.zero_mod]
  omega

theorem one_le_geom {q k : ℕ} (hk : 1 ≤ k) : 1 ≤ geom q k := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [geom_succ]
  omega

theorem geom_eq_one {q k : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k) (h : geom q k = 1) : k = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [geom_succ] at h
  have : q * geom q k = 0 := by omega
  rcases Nat.mul_eq_zero.1 this with h0 | h0
  · omega
  · cases k with
    | zero => rfl
    | succ k => have := one_le_geom (q := q) (k := k + 1) (by omega); omega

theorem two_pow_odd {e : ℕ} (h : 2 ^ e % 2 = 1) : e = 0 := by
  by_contra he
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  rw [pow_succ] at h
  omega

theorem two_pow_eq {n c : ℕ} (h : n ≤ c) : 2 ^ c = 2 ^ n * 2 ^ (c - n) := by
  rw [← pow_add, Nat.add_sub_cancel' h]

theorem exponent_eq {n k j d : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) (hj1 : 1 ≤ j) (hjq : j < 2 ^ n)
    (hdj : d + 1 = j * geom (2 ^ n) k)
    (hd : (∃ a, d = 2 ^ a) ∨ ∃ a b, a < b ∧ d = 2 ^ a + 2 ^ b) :
    (k = 2 ∧ d = 2 ^ n) ∨ (k = 2 ∧ 2 ≤ n ∧ d = 1 + 2 ^ (n + 1)) ∨
      (k = 3 ∧ d = 2 ^ n + 2 ^ (2 * n)) := by
  set q := 2 ^ n with hqdef
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hqev : q % 2 = 0 := by
    rw [hqdef]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ]
    omega
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set G := geom q k' with hGdef
  have hG1 : 1 ≤ G := one_le_geom (by omega)
  have hGodd : G % 2 = 1 := geom_odd hqev (by omega)
  have hdj' : d + 1 = j + q * (j * G) := by rw [hdj, geom_succ]; ring
  have hqpos : 0 < q := by omega
  have hmod : (d + 1) % q = j := by
    rw [hdj', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hjq]
  have hdiv : (d + 1) / q = j * G := by
    rw [hdj', Nat.add_mul_div_left _ _ hqpos, Nat.div_eq_of_lt hjq, zero_add]
  have hlow : 1 + q ≤ d + 1 := by
    rw [hdj']
    have : q ≤ q * (j * G) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hj1 hG1)
    omega
  have hk2 : G = 1 → k' = 1 := fun h => geom_eq_one (by omega) (by omega) h
  have hdec : ∀ r y, r < q → d + 1 = r + q * y → j = r ∧ j * G = y := by
    intro r y hr h
    refine ⟨?_, ?_⟩
    · rw [← hmod, h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    · rw [← hdiv, h, Nat.add_mul_div_left _ _ hqpos, Nat.div_eq_of_lt hr, zero_add]
  have hsmall : ∀ c, c < n → 2 * 2 ^ c ≤ q := by
    intro c hc
    rw [hqdef, ← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) hc
  rcases hd with ⟨a, rfl⟩ | ⟨a, b, hab, rfl⟩
  ·
    have ha : n ≤ a := by
      by_contra h
      push Not at h
      have := hsmall a h
      have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      omega
    have e1 : 2 ^ a + 1 = 1 + q * 2 ^ (a - n) := by rw [two_pow_eq ha]; ring
    obtain ⟨hj, hjG⟩ := hdec 1 (2 ^ (a - n)) (by omega) e1
    rw [hj, one_mul] at hjG
    have he : a - n = 0 := two_pow_odd (by rw [← hjG]; exact hGodd)
    have ha' : a = n := by omega
    left
    refine ⟨by rw [hk2 (by rw [hjG, he, pow_zero])], by rw [ha']⟩
  ·
    have hb : n ≤ b := by
      by_contra h
      push Not at h
      have h1 := hsmall b h
      have h2 : 2 * 2 ^ a ≤ 2 ^ b := by
        rw [← pow_succ']
        exact Nat.pow_le_pow_right (by norm_num) hab
      have h3 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      omega
    by_cases ha0 : a = 0
    ·
      subst ha0
      have e1 : 2 ^ 0 + 2 ^ b + 1 = 2 + q * 2 ^ (b - n) := by rw [two_pow_eq hb]; ring
      by_cases hn1 : n = 1
      ·
        have hq : q = 2 := by rw [hqdef, hn1]; norm_num
        have : (2 ^ 0 + 2 ^ b + 1) % q = 0 := by
          rw [e1, Nat.add_mul_mod_self_left, hq]
        rw [hmod] at this
        omega
      · have hq4 : 4 ≤ q := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        obtain ⟨hj, hjG⟩ := hdec 2 (2 ^ (b - n)) (by omega) e1
        rw [hj] at hjG
        have hbn : 1 ≤ b - n := by
          by_contra h
          have h0 : b - n = 0 := by omega
          rw [h0, pow_zero] at hjG
          omega
        have hG : G = 2 ^ (b - n - 1) := by
          rw [show b - n = b - n - 1 + 1 by omega, pow_succ] at hjG
          omega
        have he : b - n - 1 = 0 := two_pow_odd (by rw [← hG]; exact hGodd)
        right; left
        refine ⟨by rw [hk2 (by rw [hG, he, pow_zero])], by omega, ?_⟩
        rw [pow_zero, show b = n + 1 by omega]
    ·
      by_cases han : a < n
      ·
        have e1 : 2 ^ a + 2 ^ b + 1 = (1 + 2 ^ a) + q * 2 ^ (b - n) := by
          rw [two_pow_eq hb]; ring
        have hsm : 1 + 2 ^ a < q := by
          have := hsmall a han
          have : 2 ≤ 2 ^ a := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        obtain ⟨hj, hjG⟩ := hdec (1 + 2 ^ a) (2 ^ (b - n)) hsm e1
        rw [hj] at hjG
        exfalso
        have hdvd : 1 + 2 ^ a ∣ 2 ^ (b - n) := ⟨G, hjG.symm⟩
        have hodd : Nat.Coprime (1 + 2 ^ a) 2 := by
          rw [Nat.coprime_two_right]
          obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          rw [pow_succ]
          exact ⟨2 ^ a', by ring⟩
        have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right (b - n) hodd) hdvd
        have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
        omega
      ·
        push Not at han
        have e1 : 2 ^ a + 2 ^ b + 1 = 1 + q * (2 ^ (a - n) + 2 ^ (b - n)) := by
          rw [two_pow_eq han, two_pow_eq hb]; ring
        obtain ⟨hj, hjG⟩ := hdec 1 (2 ^ (a - n) + 2 ^ (b - n)) (by omega) e1
        rw [hj, one_mul] at hjG
        have ha' : a - n = 0 := by
          by_contra h
          obtain ⟨e, he⟩ : ∃ e, a - n = e + 1 := ⟨a - n - 1, by omega⟩
          obtain ⟨e', he'⟩ : ∃ e', b - n = e' + 1 := ⟨b - n - 1, by omega⟩
          rw [he, he', pow_succ, pow_succ] at hjG
          omega
        rw [ha', pow_zero] at hjG
        have hbn : 1 ≤ b - n := by omega
        obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
        have hk'' : 1 ≤ k'' := by
          by_contra h
          have : k'' = 0 := by omega
          subst this
          rw [hGdef, geom_one] at hjG
          have : 1 ≤ 2 ^ (b - n) := Nat.one_le_two_pow
          omega
        have hG' := geom_succ q k''
        rw [← hGdef, hjG] at hG'
        have hG'odd : geom q k'' % 2 = 1 := geom_odd hqev hk''
        have h2 : 2 ^ (b - n) = q * geom q k'' := by omega
        have hb2 : 2 * n ≤ b := by
          by_contra h
          push Not at h
          have h3 : 2 ^ (b - n) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
          have h4 : q ≤ q * geom q k'' := Nat.le_mul_of_pos_right _ (one_le_geom hk'')
          omega
        have h5 : 2 ^ (b - n) = q * 2 ^ (b - 2 * n) := by
          rw [hqdef, ← pow_add]
          congr 1
          omega
        have hG'' : geom q k'' = 2 ^ (b - 2 * n) := by
          rw [h5] at h2
          exact (Nat.eq_of_mul_eq_mul_left hqpos h2).symm
        have he : b - 2 * n = 0 := two_pow_odd (by rw [← hG'']; exact hG'odd)
        have hk3 : k'' = 1 := geom_eq_one (q := q) (by omega) hk'' (by rw [hG'', he, pow_zero])
        right; right
        refine ⟨by rw [hk3], ?_⟩
        rw [show a = n by omega, show b = 2 * n by omega]

end CFSG.Timmesfeld.ARS.CaseH

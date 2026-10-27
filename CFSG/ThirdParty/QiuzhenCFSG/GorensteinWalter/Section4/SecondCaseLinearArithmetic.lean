module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: arithmetic core of the linear contradiction

This module isolates the pure numeric reduction of Bender's Section 4,
equations (10)--(12).  The later group-theoretic lane supplies the
parameters `q`, `k`, `k'`, `p`, `p₀`, `p₁`, `u`, the index `m = |G : M|`,
the conjugate-count `L`, the equations

* (10) `q k' m ≤ 6 k² u³ p₀³`,
* (11) `(p₁ - 1) q k' L ≤ m`,

and the parameter relations

* `k ≤ (q+1)/2`, `(q-1)/2 ≤ k'`, `q ≥ 7`,
* `3 ≤ p₀ ≤ p₁`, `p₀ ≤ p`, `2p ≤ k`, `u ≤ p`,

all in `ℚ`; this file derives the source's final contradiction.
Equation (12) is derived from (10) and (11) exactly as in the paper:
multiply (11) by `q k'` and chain with (10).
-/

noncomputable section

namespace CFSG.GorensteinWalter

open scoped Matrix

universe u

/-! ## Private rational bounds -/

/-- The division step from equation (12) to the middle inequality of the
final chain: `A ≤ B` where `A = L/p₀` is the left-hand side and `B` is the
bound obtained from the parameter inequalities. -/
private theorem middle_bound
    {q k k' p0 p1 u L A B : ℚ}
    (hqpos : 0 < q) (hk'pos : 0 < k') (hp0pos : 0 < p0)
    (hp1m : 0 < p1 - 1)
    (hA : A = L / p0)
    (hB : B = 6 * (k * u / (q * k')) ^ 2 * u * p0 * (p0 / (p1 - 1)))
    (h12 : q * k' * (p1 - 1) * q * k' * L ≤
      6 * k ^ 2 * u ^ 3 * p0 ^ 3) :
    A ≤ B := by
  have hL : L = p0 * A := by
    rw [hA]
    field_simp [ne_of_gt hp0pos]
  have hpoly0 : q ^ 2 * k' ^ 2 * (p1 - 1) * (p0 * A) ≤
      6 * k ^ 2 * u ^ 3 * p0 ^ 3 := by
    have h12' : q ^ 2 * k' ^ 2 * (p1 - 1) * L ≤
        6 * k ^ 2 * u ^ 3 * p0 ^ 3 := by
      ring_nf at h12 ⊢
      exact h12
    rw [hL] at h12'
    exact h12'
  have hpoly : q ^ 2 * k' ^ 2 * (p1 - 1) * A ≤
      6 * k ^ 2 * u ^ 3 * p0 ^ 2 := by
    have hdiv := div_le_div_of_nonneg_right hpoly0 (le_of_lt hp0pos)
    field_simp [ne_of_gt hp0pos] at hdiv
    ring_nf at hdiv ⊢
    exact hdiv
  have hBeq : (q ^ 2 * k' ^ 2 * (p1 - 1)) * B =
      6 * k ^ 2 * u ^ 3 * p0 ^ 2 := by
    rw [hB]
    have hqk'ne : q * k' ≠ 0 := by positivity
    have hp1mne : p1 - 1 ≠ 0 := ne_of_gt hp1m
    field_simp [hqk'ne, hp1mne]
  have hDpos : 0 < q ^ 2 * k' ^ 2 * (p1 - 1) := by positivity
  nlinarith [hpoly, hBeq, hDpos]

/-- The lower bound in the final chain:
`2/9·q(q−1) − 2/3 ≤ A`. -/
private theorem lower_bound
    {q k' p p0 p1 A : ℚ}
    (hq : 7 ≤ q) (hk' : (q - 1) / 2 ≤ k')
    (hp0 : 3 ≤ p0) (hp01 : p0 ≤ p1) (hp0p : p0 ≤ p)
    (hA : A = (p1 - 1) / p0 * (q * k' - 1) -
      (q - 1) / (p * p0) * q) :
    (2 : ℚ) / 9 * q * (q - 1) - (2 : ℚ) / 3 ≤ A := by
  have hqpos : 0 < q := by linarith
  have hk'pos : 0 < k' := by nlinarith [hq, hk']
  have hp0pos : 0 < p0 := by linarith
  have hp1m : 0 < p1 - 1 := by nlinarith [hp0, hp01]
  have hqk'1 : 0 < q * k' - 1 := by nlinarith [hq, hk']
  have hfrac : (2 : ℚ) / 3 ≤ (p1 - 1) / p0 := by
    rw [le_div_iff₀ hp0pos]
    nlinarith [hp0, hp01]
  have hterm1 : (2 : ℚ) / 3 * (q * k' - 1) ≤
      (p1 - 1) / p0 * (q * k' - 1) :=
    mul_le_mul_of_nonneg_right hfrac (le_of_lt hqk'1)
  have hqk'lower : q * ((q - 1) / 2) - 1 ≤ q * k' - 1 := by
    have hmul : q * ((q - 1) / 2) ≤ q * k' :=
      mul_le_mul_of_nonneg_left hk' (le_of_lt hqpos)
    linarith
  have hbasepos : 0 ≤ q * ((q - 1) / 2) - 1 := by
    nlinarith [hq]
  have hterm1base : (2 : ℚ) / 3 * (q * ((q - 1) / 2) - 1) ≤
      (2 : ℚ) / 3 * (q * k' - 1) :=
    mul_le_mul_of_nonneg_left hqk'lower (by norm_num)
  have hpp : 9 ≤ p * p0 := by nlinarith [hp0, hp0p]
  have hdenpos : 0 < p * p0 := by positivity
  have hrec : (q - 1) / (p * p0) ≤ (q - 1) / 9 := by
    have hq1pos : 0 ≤ q - 1 := by linarith
    rw [div_le_div_iff₀ hdenpos (by norm_num : 0 < (9 : ℚ))]
    nlinarith [hpp, hq1pos]
  have hrecq : (q - 1) / (p * p0) * q ≤ (q - 1) / 9 * q :=
    mul_le_mul_of_nonneg_right hrec (le_of_lt hqpos)
  have hterm2 : -((q - 1) / 9 * q) ≤ -((q - 1) / (p * p0) * q) := by
    linarith
  have hLHS : (2 : ℚ) / 9 * q * (q - 1) - (2 : ℚ) / 3 =
      (2 : ℚ) / 3 * (q * ((q - 1) / 2) - 1) - (q - 1) / 9 * q := by
    ring_nf
  rw [hA]
  nlinarith [hterm1base, hterm1, hterm2, hLHS, hbasepos]

/-- The upper bound in the final chain: `B ≤ (q+1)²/9`. -/
private theorem upper_bound
    {q k k' p p0 p1 u B : ℚ}
    (hq : 7 ≤ q) (hk : k ≤ (q + 1) / 2) (hk' : (q - 1) / 2 ≤ k')
    (hp0 : 3 ≤ p0) (hp01 : p0 ≤ p1) (hp0p : p0 ≤ p)
    (hpk : 2 * p ≤ k) (hu : u ≤ p) (hu_nonneg : 0 ≤ u)
    (hB : B = 6 * (k * u / (q * k')) ^ 2 * u * p0 * (p0 / (p1 - 1))) :
    B ≤ (1 : ℚ) / 9 * (q + 1) ^ 2 := by
  have hqpos : 0 < q := by linarith
  have hk'pos : 0 < k' := by nlinarith [hq, hk']
  have hp0pos : 0 < p0 := by linarith
  have hp1m : 0 < p1 - 1 := by nlinarith [hp0, hp01]
  have hkpos : 0 < k := by nlinarith [hp0, hp0p, hpk]
  have hpk2 : p ≤ k / 2 := by linarith
  have hp0le : p0 ≤ k / 2 := hp0p.trans hpk2
  have hfrac : p0 / (p1 - 1) ≤ (3 : ℚ) / 2 := by
    rw [div_le_iff₀ hp1m]
    nlinarith [hp0, hp01]
  have hpow1 : u ^ 3 * (p0 ^ 2 / (p1 - 1)) ≤
      (k / 2) ^ 3 * ((k / 2) * ((3 : ℚ) / 2)) := by
    have hu3 : u ^ 3 ≤ p ^ 3 :=
      pow_le_pow_left₀ hu_nonneg hu 3
    have hp03 : p0 ^ 2 / (p1 - 1) ≤ (k / 2) * ((3 : ℚ) / 2) := by
      have hp0sq : p0 * (p0 / (p1 - 1)) ≤ p0 * ((3 : ℚ) / 2) :=
        mul_le_mul_of_nonneg_left hfrac (le_of_lt hp0pos)
      have hp0p : p0 * ((3 : ℚ) / 2) ≤ (k / 2) * ((3 : ℚ) / 2) :=
        mul_le_mul_of_nonneg_right hp0le (by norm_num : 0 ≤ (3 : ℚ) / 2)
      have hsq : p0 ^ 2 / (p1 - 1) = p0 * (p0 / (p1 - 1)) := by
        field_simp [ne_of_gt hp0pos, ne_of_gt hp1m]
      rw [hsq]
      exact hp0sq.trans hp0p
    have hp3 : p ^ 3 ≤ (k / 2) ^ 3 :=
      pow_le_pow_left₀ (by linarith [hpk2, hkpos]) hpk2 3
    exact mul_le_mul (hu3.trans hp3) hp03 (by positivity) (by positivity)
  have hBrew : B ≤ 6 * (k / (q * k')) ^ 2 * (k / 2) ^ 3 *
      ((k / 2) * ((3 : ℚ) / 2)) := by
    rw [hB]
    have hpow2 : (k * u / (q * k')) ^ 2 * u * p0 * (p0 / (p1 - 1)) =
        (k / (q * k')) ^ 2 * (u ^ 3 * (p0 ^ 2 / (p1 - 1))) := by
      field_simp [ne_of_gt hqpos, ne_of_gt hk'pos, ne_of_gt hp0pos,
        ne_of_gt hp1m]
    have hle1 : (k * u / (q * k')) ^ 2 * u * p0 * (p0 / (p1 - 1)) ≤
        (k / (q * k')) ^ 2 * ((k / 2) ^ 3 * ((k / 2) * ((3 : ℚ) / 2))) := by
      rw [hpow2]
      gcongr
    nlinarith
  have hhalfpos : 0 < (q - 1) / 2 := by linarith
  have hratio : k / (q * k') ≤
      ((q + 1) / 2) / (q * ((q - 1) / 2)) := by
    rw [div_le_div_iff₀ (mul_pos hqpos hk'pos) (mul_pos hqpos hhalfpos)]
    have hcross : k * ((q - 1) / 2) ≤ ((q + 1) / 2) * k' := by
      calc
        k * ((q - 1) / 2) ≤ ((q + 1) / 2) * ((q - 1) / 2) := by
          exact mul_le_mul_of_nonneg_right hk (le_of_lt hhalfpos)
        _ ≤ ((q + 1) / 2) * k' := by
          exact mul_le_mul_of_nonneg_left hk' (by positivity)
    nlinarith
  have hkhalf : k / 2 ≤ ((q + 1) / 2) / 2 := by linarith
  have hbound : 6 * (k / (q * k')) ^ 2 * (k / 2) ^ 3 *
      ((k / 2) * ((3 : ℚ) / 2)) ≤
      6 * (((q + 1) / 2) / (q * ((q - 1) / 2))) ^ 2 *
        (((q + 1) / 2) / 2) ^ 3 *
          ((((q + 1) / 2) / 2) * ((3 : ℚ) / 2)) := by
    gcongr
  have hfinal' : 6 * (((q + 1) / 2) / (q * ((q - 1) / 2))) ^ 2 *
      (((q + 1) / 2) / 2) ^ 3 *
        ((((q + 1) / 2) / 2) * ((3 : ℚ) / 2)) ≤
      (1 : ℚ) / 9 * (q + 1) ^ 2 := by
    have hq1pos : 0 < q - 1 := by linarith
    field_simp [ne_of_gt hqpos, ne_of_gt hq1pos]
    ring_nf
    have hq2 : 49 ≤ q ^ 2 := by nlinarith [hq]
    have hq3 : 343 ≤ q ^ 3 := by nlinarith [hq]
    have hq4 : 2401 ≤ q ^ 4 := by nlinarith [hq]
    nlinarith [hq, hq2, hq3, hq4]
  exact hBrew.trans (hbound.trans hfinal')

/-- The final rational estimate contradicts `q ≥ 7`. -/
private theorem contradiction_of_chain {q : ℚ}
    (hq : 7 ≤ q)
    (h : (2 : ℚ) / 9 * q * (q - 1) - (2 : ℚ) / 3 ≤
      (1 : ℚ) / 9 * (q + 1) ^ 2) :
    False := by
  have h9 : (9 : ℚ) ≠ 0 := by norm_num
  have h1 := h
  field_simp [h9] at h1
  ring_nf at h1
  have hq2 : 49 ≤ q ^ 2 := by nlinarith [hq]
  have hq3 : 343 ≤ q ^ 3 := by nlinarith [hq]
  have hq4 : 2401 ≤ q ^ 4 := by nlinarith [hq]
  nlinarith [h1, hq, hq2, hq3, hq4]

/-! ## Public theorem -/

/-- The Section-4 linear arithmetic core.  Equations (10) and (11) are the
explicit hypotheses; equation (12) is derived by multiplying (11) by
`q k'` and chaining with (10), exactly as in the paper.  The parameter
relations are pinned explicitly. -/
public theorem secondCase_linearArithmetic
    {q k k' p p0 p1 u m L : ℚ}
    (hq : 7 ≤ q)
    (hk : k ≤ (q + 1) / 2)
    (hk' : (q - 1) / 2 ≤ k')
    (hp0 : 3 ≤ p0) (hp01 : p0 ≤ p1) (hp0p : p0 ≤ p)
    (hpk : 2 * p ≤ k) (hu : u ≤ p) (hu_nonneg : 0 ≤ u)
    (hL : L = (p1 - 1) * (q * k' - 1) - (q - 1) / p * q)
    (h10 : q * k' * m ≤ 6 * k ^ 2 * u ^ 3 * p0 ^ 3)
    (h11 : (p1 - 1) * q * k' * L ≤ m) :
    LinearCaseContradictionData := by
  have hqpos : 0 < q := by linarith
  have hk'pos : 0 < k' := by nlinarith [hq, hk']
  have hp0pos : 0 < p0 := by linarith
  have hp1m : 0 < p1 - 1 := by nlinarith [hp0, hp01]
  -- equation (12)
  have h12 : q * k' * (p1 - 1) * q * k' * L ≤
      6 * k ^ 2 * u ^ 3 * p0 ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left h11 (by positivity : 0 ≤ q * k')
    have hmul' : q * k' * (p1 - 1) * q * k' * L ≤ q * k' * m := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    exact le_trans hmul' h10
  let A : ℚ := (p1 - 1) / p0 * (q * k' - 1) - (q - 1) / (p * p0) * q
  let B : ℚ := 6 * (k * u / (q * k')) ^ 2 * u * p0 * (p0 / (p1 - 1))
  have hA : A = L / p0 := by
    dsimp [A]
    rw [hL]
    field_simp [ne_of_gt hp0pos]
  have hB : B = 6 * (k * u / (q * k')) ^ 2 * u * p0 * (p0 / (p1 - 1)) := by
    rfl
  have hAexpr : A = (p1 - 1) / p0 * (q * k' - 1) -
      (q - 1) / (p * p0) * q := by
    rw [hA, hL]
    field_simp [ne_of_gt hp0pos]
  have hMid : A ≤ B :=
    middle_bound hqpos hk'pos hp0pos hp1m hA hB h12
  have hLow : (2 : ℚ) / 9 * q * (q - 1) - (2 : ℚ) / 3 ≤ A := by
    exact lower_bound hq hk' hp0 hp01 hp0p hAexpr
  have hUp : B ≤ (1 : ℚ) / 9 * (q + 1) ^ 2 :=
    upper_bound hq hk hk' hp0 hp01 hp0p hpk hu hu_nonneg hB
  have hchain : (2 : ℚ) / 9 * q * (q - 1) - (2 : ℚ) / 3 ≤
      (1 : ℚ) / 9 * (q + 1) ^ 2 :=
    le_trans (le_trans hLow hMid) hUp
  exact False.elim (contradiction_of_chain hq hchain)

end CFSG.GorensteinWalter

module

public import CFSG.LocalAnalysis.StandardType.GGLatticeRootsDefs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType

private def l05nK43bB {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℤ) (v w : Fin m → ℤ) : ℤ :=
  v ⬝ᵥ Q.mulVec w

private def l05nK43bN {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℤ) (v : Fin m → ℤ) : ℤ :=
  l05nK43bB Q v v

private lemma l05nK43bB_symm {m : ℕ} {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : GGLatForm Q)
    (v w : Fin m → ℤ) : l05nK43bB Q v w = l05nK43bB Q w v := by
  unfold l05nK43bB
  calc v ⬝ᵥ Q.mulVec w = v ⬝ᵥ Q.transpose.mulVec w := by rw [hQ.1]
    _ = w ⬝ᵥ Q.mulVec v := Matrix.dotProduct_transpose_mulVec Q v w

private lemma l05nK43bN_expand {m : ℕ} {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : GGLatForm Q)
    (v w : Fin m → ℤ) :
    l05nK43bN Q (l05nK43bN Q w • v - l05nK43bB Q v w • w) =
      l05nK43bN Q w * (l05nK43bN Q v * l05nK43bN Q w - l05nK43bB Q v w ^ 2) := by
  have hsym : l05nK43bB Q w v = l05nK43bB Q v w := l05nK43bB_symm hQ w v
  simp only [l05nK43bN, l05nK43bB] at hsym ⊢
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hsym]
  ring

private lemma l05nK43bB_sq_le {m : ℕ} {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : GGLatForm Q)
    (v w : Fin m → ℤ) : l05nK43bB Q v w ^ 2 ≤ l05nK43bN Q v * l05nK43bN Q w := by
  by_cases hw : w = 0
  · subst hw
    simp [l05nK43bN, l05nK43bB]
  · have hNw : 0 < l05nK43bN Q w := hQ.2 w hw
    have hNy := l05nK43bN_expand hQ v w
    have hy_nonneg : 0 ≤ l05nK43bN Q (l05nK43bN Q w • v - l05nK43bB Q v w • w) := by
      by_cases hy : l05nK43bN Q w • v - l05nK43bB Q v w • w = 0
      · rw [hy]; simp [l05nK43bN, l05nK43bB]
      · exact (hQ.2 _ hy).le
    have hprod : 0 ≤ l05nK43bN Q w *
        (l05nK43bN Q v * l05nK43bN Q w - l05nK43bB Q v w ^ 2) := by
      rw [← hNy]; exact hy_nonneg
    have hX : 0 ≤ l05nK43bN Q v * l05nK43bN Q w - l05nK43bB Q v w ^ 2 := by
      nlinarith [hprod, hNw]
    linarith

private lemma l05nK43bC_mul_N {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℤ) {w : Fin m → ℤ}
    (hw : GGLatRoot Q w) (v : Fin m → ℤ) :
    ggLatCartan Q v w * l05nK43bN Q w = 2 * l05nK43bB Q v w := by
  unfold ggLatCartan l05nK43bN l05nK43bB
  exact Int.ediv_mul_cancel (hw.2 v)

private lemma l05nK43bC_swap {m : ℕ} {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : GGLatForm Q)
    {v w : Fin m → ℤ} (hv : GGLatRoot Q v) (hw : GGLatRoot Q w) :
    ggLatCartan Q v w * l05nK43bN Q w = ggLatCartan Q w v * l05nK43bN Q v := by
  rw [l05nK43bC_mul_N Q hw v, l05nK43bC_mul_N Q hv w, l05nK43bB_symm hQ v w]

private lemma l05nK43b_prod_bounds {m : ℕ} {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : GGLatForm Q)
    {v w : Fin m → ℤ} (hv : GGLatRoot Q v) (hw : GGLatRoot Q w) :
    0 ≤ ggLatCartan Q v w * ggLatCartan Q w v ∧
      ggLatCartan Q v w * ggLatCartan Q w v ≤ 4 := by
  have hNv : 0 < l05nK43bN Q v := hQ.2 v hv.1
  have hNw : 0 < l05nK43bN Q w := hQ.2 w hw.1
  have h1 : ggLatCartan Q v w * l05nK43bN Q w = 2 * l05nK43bB Q v w :=
    l05nK43bC_mul_N Q hw v
  have h2 : ggLatCartan Q w v * l05nK43bN Q v = 2 * l05nK43bB Q v w := by
    rw [l05nK43bC_mul_N Q hv w, l05nK43bB_symm hQ w v]
  have hP : (ggLatCartan Q v w * ggLatCartan Q w v) * (l05nK43bN Q v * l05nK43bN Q w) =
      4 * (l05nK43bB Q v w) ^ 2 := by
    rw [show (ggLatCartan Q v w * ggLatCartan Q w v) *
          (l05nK43bN Q v * l05nK43bN Q w) =
        (ggLatCartan Q v w * l05nK43bN Q w) *
          (ggLatCartan Q w v * l05nK43bN Q v) by ring, h1, h2]
    ring
  have hb2 : (l05nK43bB Q v w) ^ 2 ≤ l05nK43bN Q v * l05nK43bN Q w :=
    l05nK43bB_sq_le hQ v w
  constructor <;> nlinarith [hNv, hNw, hP, hb2]

private lemma l05nK43b_eq_one {m : ℕ} {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : GGLatForm Q)
    {v w : Fin m → ℤ} (hv : GGLatRoot Q v) (hw : GGLatRoot Q w)
    (h : ggLatCartan Q v w * ggLatCartan Q w v = 1) :
    ggLatCartan Q v w = ggLatCartan Q w v ∧
      (ggLatCartan Q v w = 1 ∨ ggLatCartan Q v w = -1) ∧
      l05nK43bN Q v = l05nK43bN Q w := by
  have hpm : ggLatCartan Q v w = 1 ∨ ggLatCartan Q v w = -1 :=
    Int.eq_one_or_neg_one_of_mul_eq_one h
  have hne : ggLatCartan Q v w ≠ 0 := by
    rcases hpm with h1 | h1 <;> rw [h1] <;> norm_num
  have hCwv : ggLatCartan Q w v = ggLatCartan Q v w := by
    rcases hpm with h1 | h1
    · rw [h1] at h; rw [h1]; simpa using h
    · rw [h1] at h; rw [h1]; linarith
  have hswap := l05nK43bC_swap hQ hv hw
  rw [hCwv] at hswap
  exact ⟨hCwv.symm, hpm, (mul_left_cancel₀ hne hswap).symm⟩

private lemma l05nK43b_a_mul {p : ℕ} [Fact p.Prime] {m : ℕ}
    (Q : Matrix (Fin m) (Fin m) ℤ) {v : Fin 3 → Fin m → ℤ} {μ : Fin 3 → ZMod p}
    (hμ : ∀ k, μ k ≠ 0) {a : Fin 3 → Fin 3 → ZMod p}
    (hcongr : ∀ j k, a j k * μ k = μ j * (ggLatCartan Q (v k) (v j) : ZMod p))
    (j k : Fin 3) :
    a j k * a k j =
      ((ggLatCartan Q (v k) (v j) * ggLatCartan Q (v j) (v k) : ℤ) : ZMod p) := by
  have h1 := hcongr j k
  have h2 := hcongr k j
  have hμjk : μ j * μ k ≠ 0 := mul_ne_zero (hμ j) (hμ k)
  have hcast : ((ggLatCartan Q (v k) (v j) * ggLatCartan Q (v j) (v k) : ℤ) : ZMod p)
      = (ggLatCartan Q (v k) (v j) : ZMod p) * (ggLatCartan Q (v j) (v k) : ZMod p) := by
    push_cast; ring
  have hmul : (μ j * μ k) * (a j k * a k j)
      = (μ j * μ k) * ((ggLatCartan Q (v k) (v j) : ZMod p) *
          (ggLatCartan Q (v j) (v k) : ZMod p)) := by
    calc
      (μ j * μ k) * (a j k * a k j) = (a j k * μ k) * (a k j * μ j) := by ring
      _ = (μ j * (ggLatCartan Q (v k) (v j) : ZMod p)) *
            (μ k * (ggLatCartan Q (v j) (v k) : ZMod p)) := by rw [h1, h2]
      _ = (μ j * μ k) * ((ggLatCartan Q (v k) (v j) : ZMod p) *
            (ggLatCartan Q (v j) (v k) : ZMod p)) := by ring
  rw [hcast]
  exact mul_left_cancel₀ hμjk hmul

private lemma l05nK43b_a_cyc {p : ℕ} [Fact p.Prime] {m : ℕ}
    (Q : Matrix (Fin m) (Fin m) ℤ) {v : Fin 3 → Fin m → ℤ} {μ : Fin 3 → ZMod p}
    (hμ : ∀ k, μ k ≠ 0) {a : Fin 3 → Fin 3 → ZMod p}
    (hcongr : ∀ j k, a j k * μ k = μ j * (ggLatCartan Q (v k) (v j) : ZMod p)) :
    a 1 0 * a 2 1 * a 0 2 =
      ((ggLatCartan Q (v 0) (v 1) * ggLatCartan Q (v 1) (v 2) *
        ggLatCartan Q (v 2) (v 0) : ℤ) : ZMod p) := by
  have h1 := hcongr 1 0
  have h2 := hcongr 2 1
  have h3 := hcongr 0 2
  have hμ012 : μ 0 * μ 1 * μ 2 ≠ 0 := by
    have h01 := mul_ne_zero (hμ 0) (hμ 1)
    exact mul_ne_zero h01 (hμ 2)
  have hcast : ((ggLatCartan Q (v 0) (v 1) * ggLatCartan Q (v 1) (v 2) *
      ggLatCartan Q (v 2) (v 0) : ℤ) : ZMod p)
      = (ggLatCartan Q (v 0) (v 1) : ZMod p) * (ggLatCartan Q (v 1) (v 2) : ZMod p) *
        (ggLatCartan Q (v 2) (v 0) : ZMod p) := by
    push_cast; ring
  have hmul : (μ 0 * μ 1 * μ 2) * (a 1 0 * a 2 1 * a 0 2)
      = (μ 0 * μ 1 * μ 2) * ((ggLatCartan Q (v 0) (v 1) : ZMod p) *
          (ggLatCartan Q (v 1) (v 2) : ZMod p) * (ggLatCartan Q (v 2) (v 0) : ZMod p)) := by
    calc
      (μ 0 * μ 1 * μ 2) * (a 1 0 * a 2 1 * a 0 2)
          = (a 1 0 * μ 0) * (a 2 1 * μ 1) * (a 0 2 * μ 2) := by ring
      _ = (μ 1 * (ggLatCartan Q (v 0) (v 1) : ZMod p)) *
            (μ 2 * (ggLatCartan Q (v 1) (v 2) : ZMod p)) *
            (μ 0 * (ggLatCartan Q (v 2) (v 0) : ZMod p)) := by rw [h1, h2, h3]
      _ = (μ 0 * μ 1 * μ 2) * ((ggLatCartan Q (v 0) (v 1) : ZMod p) *
            (ggLatCartan Q (v 1) (v 2) : ZMod p) *
            (ggLatCartan Q (v 2) (v 0) : ZMod p)) := by ring
  rw [hcast]
  exact mul_left_cancel₀ hμ012 hmul

private lemma l05nK43b_intCast_eq_one {p : ℕ} (hp5 : 5 ≤ p) {P : ℤ} (h0 : 0 ≤ P) (h4 : P ≤ 4)
    (h : (P : ZMod p) = 1) : P = 1 := by
  have hp5' : (5 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp5
  have hp1 : (1 : ℤ) < (p : ℤ) := by omega
  have hPlt : P < (p : ℤ) := by omega
  have hmod : P % (p : ℤ) = (1 : ℤ) % (p : ℤ) :=
    (ZMod.intCast_eq_intCast_iff' P 1 p).mp (by simpa using h)
  rw [Int.emod_eq_of_lt h0 hPlt, Int.emod_eq_of_lt (by norm_num) hp1] at hmod
  omega

private lemma l05nK43b_sq_mem {x : ℤ} (h4 : x ^ 2 ≤ 4) :
    x ^ 2 = 0 ∨ x ^ 2 = 1 ∨ x ^ 2 = 4 := by
  have hxle : x ≤ 2 := by nlinarith [sq_nonneg (x - 2)]
  have hxge : -2 ≤ x := by nlinarith [sq_nonneg (x + 2)]
  interval_cases x <;> norm_num

private lemma l05nK43b_pm_mul {p : ℕ} {x y z : ℤ} (hx : x = 1 ∨ x = -1)
    (hy : y = 1 ∨ y = -1) (hz : z = 1 ∨ z = -1) :
    (x : ZMod p) * (y : ZMod p) * (z : ZMod p) = 1 ∨
      (x : ZMod p) * (y : ZMod p) * (z : ZMod p) = -1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    simp

private lemma l05nK43b_field_contradiction {p : ℕ} [Fact p.Prime] {ζ : ZMod p}
    (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) (hζ2 : ζ ≠ -1)
    {c01 c10 c12 c21 c02 c20 : ℤ}
    (hP01 : c10 * c01 = 1) (hP12 : c21 * c12 = 1)
    (hc02c20 : c02 = c20)
    (hc02sq_le : c02 ^ 2 ≤ 4)
    (h02 : ((c02 * c20 : ℤ) : ZMod p) = 2 + ζ + ζ⁻¹)
    (hcyc : ((c01 * c12 * c20 : ℤ) : ZMod p) = 1 + ζ⁻¹) : False := by
  have hsq : c02 * c20 = c02 ^ 2 := by rw [hc02c20]; ring
  have hmem : c02 ^ 2 = 0 ∨ c02 ^ 2 = 1 ∨ c02 ^ 2 = 4 :=
    l05nK43b_sq_mem hc02sq_le
  have hP02 : c02 * c20 = 1 := by
    rcases hmem with h0 | h1 | h4
    · exfalso
      have hh : 2 + ζ + ζ⁻¹ = 0 := by
        have hc : ((c02 * c20 : ℤ) : ZMod p) = 0 := by rw [hsq, h0]; simp
        rw [h02] at hc; exact hc
      have hz : (ζ + 1) ^ 2 = 0 := by
        have hh' := hh
        field_simp at hh'
        linear_combination hh'
      have hz1 : ζ + 1 = 0 := (pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num)).mp hz
      exact hζ2 (by linear_combination hz1)
    · rw [hsq, h1]
    · exfalso
      have hh : 2 + ζ + ζ⁻¹ = 4 := by
        have hc : ((c02 * c20 : ℤ) : ZMod p) = 4 := by rw [hsq, h4]; norm_num
        rw [h02] at hc; exact hc
      have hz : (ζ - 1) ^ 2 = 0 := by
        have hh' := hh
        field_simp at hh'
        linear_combination hh'
      have hz1 : ζ - 1 = 0 := (pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num)).mp hz
      exact hζ1 (by linear_combination hz1)
  have hc02sq : c02 ^ 2 = 1 := by rw [← hsq, hP02]
  have hc02pm : c02 = 1 ∨ c02 = -1 :=
    Int.eq_one_or_neg_one_of_mul_eq_one (by rw [← pow_two]; exact hc02sq)
  have hc20pm : c20 = 1 ∨ c20 = -1 := by
    rcases hc02pm with h | h
    · left; rw [← hc02c20, h]
    · right; rw [← hc02c20, h]
  have hc10pm : c10 = 1 ∨ c10 = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hP01
  have hc01pm : c01 = 1 ∨ c01 = -1 := by
    rcases hc10pm with h | h
    · left; rw [h] at hP01; simpa using hP01
    · right; rw [h] at hP01; linarith
  have hc21pm : c21 = 1 ∨ c21 = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hP12
  have hc12pm : c12 = 1 ∨ c12 = -1 := by
    rcases hc21pm with h | h
    · left; rw [h] at hP12; simpa using hP12
    · right; rw [h] at hP12; linarith
  have hcyc' : (c01 : ZMod p) * (c12 : ZMod p) * (c20 : ZMod p) = 1 + ζ⁻¹ := by
    rw [← hcyc]; push_cast; ring
  have hprodsign : (c01 : ZMod p) * (c12 : ZMod p) * (c20 : ZMod p) = 1 ∨
      (c01 : ZMod p) * (c12 : ZMod p) * (c20 : ZMod p) = -1 :=
    l05nK43b_pm_mul hc01pm hc12pm hc20pm
  have hsum : 1 + ζ⁻¹ = 1 ∨ 1 + ζ⁻¹ = -1 := by
    rcases hprodsign with hh | hh
    · left; rw [← hcyc', hh]
    · right; rw [← hcyc', hh]
  have h02' : 2 + ζ + ζ⁻¹ = 1 := by
    rw [← h02, hP02]; simp
  rcases hsum with hh | hh
  · have hz : ζ⁻¹ = 0 := by linear_combination hh
    exact inv_ne_zero hζ0 hz
  · have hz : ζ = 1 := by linear_combination h02' - hh
    exact hζ1 hz

theorem ggRC_triangle_not_lattice {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {ζ : ZMod p}
    (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) (hζ2 : ζ ≠ -1)
    {m : ℕ} {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : GGLatForm Q) {v : Fin 3 → Fin m → ℤ}
    (hv : ∀ k, GGLatRoot Q (v k)) {μ : Fin 3 → ZMod p} (hμ : ∀ k, μ k ≠ 0)
    {a : Fin 3 → Fin 3 → ZMod p}
    (hcongr : ∀ j k, a j k * μ k = μ j * (ggLatCartan Q (v k) (v j) : ZMod p))
    (h01 : a 0 1 * a 1 0 = 1) (h12 : a 1 2 * a 2 1 = 1)
    (h02 : a 0 2 * a 2 0 = 2 + ζ + ζ⁻¹) (hcyc : a 1 0 * a 2 1 * a 0 2 = 1 + ζ⁻¹) : False := by
  have hP01 : ggLatCartan Q (v 1) (v 0) * ggLatCartan Q (v 0) (v 1) = 1 :=
    l05nK43b_intCast_eq_one hp5
      (l05nK43b_prod_bounds hQ (hv 1) (hv 0)).1
      (l05nK43b_prod_bounds hQ (hv 1) (hv 0)).2
      (by
        have hb5 := l05nK43b_a_mul Q hμ hcongr 0 1
        rw [← hb5, h01])
  have hP12 : ggLatCartan Q (v 2) (v 1) * ggLatCartan Q (v 1) (v 2) = 1 :=
    l05nK43b_intCast_eq_one hp5
      (l05nK43b_prod_bounds hQ (hv 2) (hv 1)).1
      (l05nK43b_prod_bounds hQ (hv 2) (hv 1)).2
      (by
        have hb5 := l05nK43b_a_mul Q hμ hcongr 1 2
        rw [← hb5, h12])
  obtain ⟨_, _, hN10⟩ := l05nK43b_eq_one hQ (hv 1) (hv 0) hP01
  obtain ⟨_, _, hN21⟩ := l05nK43b_eq_one hQ (hv 2) (hv 1) hP12
  have hN02 : l05nK43bN Q (v 0) = l05nK43bN Q (v 2) := by linarith
  have hc02c20 : ggLatCartan Q (v 0) (v 2) = ggLatCartan Q (v 2) (v 0) := by
    have hswap := l05nK43bC_swap hQ (hv 0) (hv 2)
    rw [hN02] at hswap
    exact mul_right_cancel₀ (hQ.2 (v 2) (hv 2).1).ne' hswap
  have hc02sq_le : (ggLatCartan Q (v 0) (v 2)) ^ 2 ≤ 4 := by
    have hb := (l05nK43b_prod_bounds hQ (hv 0) (hv 2)).2
    rw [← hc02c20] at hb
    simpa [pow_two] using hb
  have h02cast : ((ggLatCartan Q (v 0) (v 2) * ggLatCartan Q (v 2) (v 0) : ℤ) : ZMod p) =
      2 + ζ + ζ⁻¹ := by
    have hb5 := l05nK43b_a_mul Q hμ hcongr 0 2
    rw [show (ggLatCartan Q (v 0) (v 2) * ggLatCartan Q (v 2) (v 0) : ℤ) =
        (ggLatCartan Q (v 2) (v 0) * ggLatCartan Q (v 0) (v 2)) by ring]
    rw [← hb5, h02]
  have hcyccast : ((ggLatCartan Q (v 0) (v 1) * ggLatCartan Q (v 1) (v 2) *
      ggLatCartan Q (v 2) (v 0) : ℤ) : ZMod p) = 1 + ζ⁻¹ := by
    have hb := l05nK43b_a_cyc Q hμ hcongr
    rw [← hb, hcyc]
  exact l05nK43b_field_contradiction hζ0 hζ1 hζ2
    (c01 := ggLatCartan Q (v 0) (v 1))
    (c10 := ggLatCartan Q (v 1) (v 0))
    (c12 := ggLatCartan Q (v 1) (v 2))
    (c21 := ggLatCartan Q (v 2) (v 1))
    (c02 := ggLatCartan Q (v 0) (v 2))
    (c20 := ggLatCartan Q (v 2) (v 0))
    hP01 hP12 hc02c20 hc02sq_le h02cast hcyccast

end CFSG.StandardType

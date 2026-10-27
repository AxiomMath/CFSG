module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.PartOne.KE

abbrev EInt := ℤ × ℤ

abbrev ERow := EInt × EInt × EInt

@[expose] def eadd (x y : EInt) : EInt := (x.1 + y.1, x.2 + y.2)

@[expose] def esub (x y : EInt) : EInt := (x.1 - y.1, x.2 - y.2)

@[expose] def emul (x y : EInt) : EInt :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1 - x.2 * y.2)

@[expose] def enorm (x : EInt) : ℤ := x.1 * x.1 - x.1 * x.2 + x.2 * x.2

@[expose] def ecross (u v : ERow) : ERow :=
  (esub (emul u.2.1 v.2.2) (emul u.2.2 v.2.1), esub (emul u.2.2 v.1) (emul u.1 v.2.2),
    esub (emul u.1 v.2.1) (emul u.2.1 v.1))

@[expose] def edot (u v : ERow) : EInt :=
  eadd (eadd (emul u.1 v.1) (emul u.2.1 v.2.1)) (emul u.2.2 v.2.2)

@[expose] def edet3 (u v w : ERow) : EInt := edot w (ecross u v)

@[expose] def escale (u : EInt) (g : ERow) : ERow := (emul u g.1, emul u g.2.1, emul u g.2.2)

@[expose] def eUnits : List EInt := [(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)]

@[expose] def ENormOK (x : EInt) : Prop :=
  enorm x = 0 ∨ enorm x = 1 ∨ enorm x = 3 ∨ enorm x = 4 ∨ enorm x = 9

instance instDecidableENormOK (x : EInt) : Decidable (ENormOK x) := by
  unfold ENormOK
  infer_instance

@[expose] def RowsOK {ι : Type*} [LT ι] (g : ι → ERow) : Prop :=
  (∀ i j, i < j → ENormOK (ecross (g i) (g j)).1 ∧ ENormOK (ecross (g i) (g j)).2.1 ∧
      ENormOK (ecross (g i) (g j)).2.2 ∧ ecross (g i) (g j) ≠ ((0, 0), (0, 0), (0, 0))) ∧
    ∀ i j l, i < j → ENormOK (edet3 (g i) (g j) (g l))

instance instDecidableRowsOKFin {n : ℕ} (g : Fin n → ERow) : Decidable (RowsOK g) := by
  unfold RowsOK
  infer_instance

section Eval

variable {p : ℕ} (ρ : ZMod p)

@[expose] def ev (x : EInt) : ZMod p := (x.1 : ZMod p) + (x.2 : ZMod p) * ρ

variable {ρ}

theorem ev_eadd (x y : EInt) : ev ρ (eadd x y) = ev ρ x + ev ρ y := by
  simp only [ev, eadd]
  push_cast
  ring

theorem ev_esub (x y : EInt) : ev ρ (esub x y) = ev ρ x - ev ρ y := by
  simp only [ev, esub]
  push_cast
  ring

theorem ev_emul (hρ : ρ ^ 2 + ρ + 1 = 0) (x y : EInt) :
    ev ρ (emul x y) = ev ρ x * ev ρ y := by
  simp only [ev, emul]
  push_cast
  linear_combination (-(x.2 : ZMod p) * (y.2 : ZMod p)) * hρ

theorem intCast_enorm (hρ : ρ ^ 2 + ρ + 1 = 0) (x : EInt) :
    ((enorm x : ℤ) : ZMod p) = ev ρ x * ev ρ (x.1 - x.2, -x.2) := by
  simp only [ev, enorm]
  push_cast
  linear_combination ((x.2 : ZMod p) ^ 2) * hρ

variable [Fact p.Prime] in
theorem ev_eq_zero (hp3 : 3 < p) (hρ : ρ ^ 2 + ρ + 1 = 0) {x : EInt} (hx : ENormOK x)
    (h : ev ρ x = 0) : x = (0, 0) := by
  have hn : ((enorm x : ℤ) : ZMod p) = 0 := by rw [intCast_enorm hρ, h, zero_mul]
  have hdvd : (p : ℤ) ∣ enorm x := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hn
  have hp4 : (4 : ℤ) ≤ p := by exact_mod_cast hp3
  have hnn : 0 ≤ enorm x := by
    simp only [enorm]
    nlinarith [sq_nonneg (x.1 - x.2), sq_nonneg x.1, sq_nonneg x.2]
  have h0 : enorm x = 0 := by
    have hpp : p.Prime := Fact.out
    rcases hx with h0 | h1 | h3 | h4 | h9
    · exact h0
    · exfalso
      have := Int.le_of_dvd (by omega) (h1 ▸ hdvd)
      omega
    · exfalso
      have := Int.le_of_dvd (by omega) (h3 ▸ hdvd)
      omega
    · exfalso
      have h4' : p ∣ 4 := by exact_mod_cast (h4 ▸ hdvd : (p : ℤ) ∣ 4)
      have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) h4'
      have : p = 4 := by omega
      subst this
      exact absurd hpp (by decide)
    · exfalso
      have h9' : p ∣ 9 := by exact_mod_cast (h9 ▸ hdvd : (p : ℤ) ∣ 9)
      have hle : p ≤ 9 := Nat.le_of_dvd (by norm_num) h9'
      interval_cases p <;> first | omega | exact absurd hpp (by decide)
  have hb : x.2 = 0 := by
    have h1 : x.2 ^ 2 = 0 := by
      simp only [enorm] at h0
      nlinarith [sq_nonneg (2 * x.1 - x.2), sq_nonneg x.2]
    exact (pow_eq_zero_iff two_ne_zero).1 h1
  have ha : x.1 = 0 := by simpa [enorm, hb] using h0
  exact Prod.ext ha hb

variable [Fact p.Prime] in
theorem ev_ne_zero_of_mem_eUnits (hp3 : 3 < p) (hρ : ρ ^ 2 + ρ + 1 = 0) {u : EInt}
    (hu : u ∈ eUnits) : ev ρ u ≠ 0 := by
  intro h
  have hok : ENormOK u := by
    simp only [eUnits, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h0 := ev_eq_zero hp3 hρ hok h
  simp only [eUnits, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h0

end Eval

section Algebra

variable {F : Type*} [CommRing F] [NoZeroDivisors F]

theorem dot_iff_dot_cross {u1 u2 u3 v1 v2 v3 w1 w2 w3 a1 a2 a3 : F}
    (hu : u1 * a1 + u2 * a2 + u3 * a3 = 0) (hv : v1 * a1 + v2 * a2 + v3 * a3 = 0)
    (hc : u2 * v3 - u3 * v2 ≠ 0 ∨ u3 * v1 - u1 * v3 ≠ 0 ∨ u1 * v2 - u2 * v1 ≠ 0)
    (ha : a1 ≠ 0 ∨ a2 ≠ 0 ∨ a3 ≠ 0) :
    w1 * a1 + w2 * a2 + w3 * a3 = 0 ↔
      w1 * (u2 * v3 - u3 * v2) + w2 * (u3 * v1 - u1 * v3) + w3 * (u1 * v2 - u2 * v1) = 0 := by
  have k1 : (u2 * v3 - u3 * v2) * (w1 * a1 + w2 * a2 + w3 * a3) =
      a1 * (w1 * (u2 * v3 - u3 * v2) + w2 * (u3 * v1 - u1 * v3) + w3 * (u1 * v2 - u2 * v1)) := by
    linear_combination (w2 * v3 - w3 * v2) * hu + (w3 * u2 - w2 * u3) * hv
  have k2 : (u3 * v1 - u1 * v3) * (w1 * a1 + w2 * a2 + w3 * a3) =
      a2 * (w1 * (u2 * v3 - u3 * v2) + w2 * (u3 * v1 - u1 * v3) + w3 * (u1 * v2 - u2 * v1)) := by
    linear_combination (w3 * v1 - w1 * v3) * hu + (w1 * u3 - w3 * u1) * hv
  have k3 : (u1 * v2 - u2 * v1) * (w1 * a1 + w2 * a2 + w3 * a3) =
      a3 * (w1 * (u2 * v3 - u3 * v2) + w2 * (u3 * v1 - u1 * v3) + w3 * (u1 * v2 - u2 * v1)) := by
    linear_combination (w1 * v2 - w2 * v1) * hu + (w2 * u1 - w1 * u2) * hv
  constructor
  · intro h
    rw [h, mul_zero] at k1 k2 k3
    rcases ha with h1 | h2 | h3
    · exact (mul_eq_zero.1 k1.symm).resolve_left h1
    · exact (mul_eq_zero.1 k2.symm).resolve_left h2
    · exact (mul_eq_zero.1 k3.symm).resolve_left h3
  · intro h
    rw [h, mul_zero] at k1 k2 k3
    rcases hc with h1 | h2 | h3
    · exact (mul_eq_zero.1 k1).resolve_left h1
    · exact (mul_eq_zero.1 k2).resolve_left h2
    · exact (mul_eq_zero.1 k3).resolve_left h3

end Algebra

section Kernel

variable {ι : Type*} {p : ℕ} {ρ : ZMod p}

@[expose] def rowDot (ρ : ZMod p) (g : ERow) (a : ZMod p × ZMod p × ZMod p) : ZMod p :=
  ev ρ g.1 * a.1 + ev ρ g.2.1 * a.2.1 + ev ρ g.2.2 * a.2.2

theorem rowDot_escale (hρ : ρ ^ 2 + ρ + 1 = 0) (u : EInt) (g : ERow)
    (a : ZMod p × ZMod p × ZMod p) :
    rowDot ρ (escale u g) a = ev ρ u * rowDot ρ g a := by
  simp only [rowDot, escale, ev_emul hρ]
  ring

variable [Fact p.Prime] in
theorem rank3_kernel_aux (hp3 : 3 < p) (hρ : ρ ^ 2 + ρ + 1 = 0) {g : ι → ERow} [LT ι]
    (hg : RowsOK g) (a : ZMod p × ZMod p × ZMod p) (ha : a ≠ (0, 0, 0)) {i j : ι} (hij : i < j)
    (hi : rowDot ρ (g i) a = 0) (hj : rowDot ρ (g j) a = 0) (l : ι) :
    rowDot ρ (g l) a = 0 ↔ edet3 (g i) (g j) (g l) = (0, 0) := by
  obtain ⟨hn1, hn2, hn3, hne⟩ := hg.1 i j hij
  have hev1 : ev ρ (ecross (g i) (g j)).1 =
      ev ρ (g i).2.1 * ev ρ (g j).2.2 - ev ρ (g i).2.2 * ev ρ (g j).2.1 := by
    simp only [ecross, ev_esub, ev_emul hρ]
  have hev2 : ev ρ (ecross (g i) (g j)).2.1 =
      ev ρ (g i).2.2 * ev ρ (g j).1 - ev ρ (g i).1 * ev ρ (g j).2.2 := by
    simp only [ecross, ev_esub, ev_emul hρ]
  have hev3 : ev ρ (ecross (g i) (g j)).2.2 =
      ev ρ (g i).1 * ev ρ (g j).2.1 - ev ρ (g i).2.1 * ev ρ (g j).1 := by
    simp only [ecross, ev_esub, ev_emul hρ]
  have hdetev : ev ρ (edet3 (g i) (g j) (g l)) =
      ev ρ (g l).1 * ev ρ (ecross (g i) (g j)).1 + ev ρ (g l).2.1 * ev ρ (ecross (g i) (g j)).2.1 +
        ev ρ (g l).2.2 * ev ρ (ecross (g i) (g j)).2.2 := by
    simp only [edet3, edot, ev_eadd, ev_emul hρ]
  have hcne : ev ρ (ecross (g i) (g j)).1 ≠ 0 ∨ ev ρ (ecross (g i) (g j)).2.1 ≠ 0 ∨
      ev ρ (ecross (g i) (g j)).2.2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    exact hne (Prod.ext (ev_eq_zero hp3 hρ hn1 h1) (Prod.ext (ev_eq_zero hp3 hρ hn2 h2)
      (ev_eq_zero hp3 hρ hn3 h3)))
  have hane : a.1 ≠ 0 ∨ a.2.1 ≠ 0 ∨ a.2.2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha (Prod.ext hcon.1 (Prod.ext hcon.2.1 hcon.2.2))
  rw [hev1, hev2, hev3] at hcne
  have hi' : ev ρ (g i).1 * a.1 + ev ρ (g i).2.1 * a.2.1 + ev ρ (g i).2.2 * a.2.2 = 0 := hi
  have hj' : ev ρ (g j).1 * a.1 + ev ρ (g j).2.1 * a.2.1 + ev ρ (g j).2.2 * a.2.2 = 0 := hj
  have key : rowDot ρ (g l) a = 0 ↔ ev ρ (edet3 (g i) (g j) (g l)) = 0 := by
    rw [hdetev, hev1, hev2, hev3]
    exact dot_iff_dot_cross hi' hj' hcne hane
  refine key.trans ⟨fun h => ev_eq_zero hp3 hρ (hg.2 i j l hij) h, fun h => ?_⟩
  rw [h]
  simp [ev]

variable [Fact p.Prime] in
theorem rank3_kernel (hp3 : 3 < p) (hρ : ρ ^ 2 + ρ + 1 = 0) {g : ι → ERow} [LinearOrder ι]
    (hg : RowsOK g) (a : ZMod p × ZMod p × ZMod p) (ha : a ≠ (0, 0, 0)) :
    (∀ l, rowDot ρ (g l) a ≠ 0) ∨ (∃ k, ∀ l, rowDot ρ (g l) a = 0 ↔ l = k) ∨
      ∃ i j, i < j ∧ ∀ l, rowDot ρ (g l) a = 0 ↔ edet3 (g i) (g j) (g l) = (0, 0) := by
  classical
  by_cases hex : ∃ i j, i ≠ j ∧ rowDot ρ (g i) a = 0 ∧ rowDot ρ (g j) a = 0
  · refine Or.inr (Or.inr ?_)
    obtain ⟨i, j, hij, hi, hj⟩ := hex
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, rank3_kernel_aux hp3 hρ hg a ha h hi hj⟩
    · exact ⟨j, i, h, rank3_kernel_aux hp3 hρ hg a ha h hj hi⟩
  · push Not at hex
    by_cases hne : ∃ k, rowDot ρ (g k) a = 0
    · obtain ⟨k, hk⟩ := hne
      refine Or.inr (Or.inl ⟨k, fun l => ⟨fun hl => ?_, fun h => h ▸ hk⟩⟩)
      by_contra hlk
      exact hex l k hlk hl hk
    · push Not at hne
      exact Or.inl hne

end Kernel

end CFSG.RankThree.PartOne.KE

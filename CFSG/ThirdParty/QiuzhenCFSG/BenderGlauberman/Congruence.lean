module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Mod-2 congruence for complex character values

For algebraic integers `a, b`, the paper writes `a ≡ b` for congruence modulo
`2` in the ring of algebraic integers: `a - b = 2·w` for some algebraic
integer `w`.
-/

noncomputable section

namespace CFSG.BenderGlauberman

/-- `a ≡ b (mod 2)`: `a - b` is twice an algebraic integer. -/
@[expose]
public def CongruentModTwo (a b : ℂ) : Prop :=
  ∃ w : ℂ, IsIntegral ℤ w ∧ a - b = 2 * w

namespace CongruentModTwo

public lemma refl (a : ℂ) : CongruentModTwo a a :=
  ⟨0, isIntegral_zero, by ring⟩

public lemma symm {a b : ℂ} (h : CongruentModTwo a b) : CongruentModTwo b a := by
  rcases h with ⟨w, hw, hw'⟩
  refine ⟨-w, hw.neg, ?_⟩
  calc
    b - a = -(a - b) := by ring
    _ = -(2 * w) := by rw [hw']
    _ = 2 * (-w) := by ring

public lemma trans {a b c : ℂ} (h1 : CongruentModTwo a b) (h2 : CongruentModTwo b c) :
    CongruentModTwo a c := by
  rcases h1 with ⟨w1, hw1, hw1'⟩
  rcases h2 with ⟨w2, hw2, hw2'⟩
  refine ⟨w1 + w2, hw1.add hw2, ?_⟩
  calc
    a - c = (a - b) + (b - c) := by ring
    _ = 2 * w1 + 2 * w2 := by rw [hw1', hw2']
    _ = 2 * (w1 + w2) := by ring

public lemma add {a b c d : ℂ} (h1 : CongruentModTwo a b) (h2 : CongruentModTwo c d) :
    CongruentModTwo (a + c) (b + d) := by
  rcases h1 with ⟨w1, hw1, hw1'⟩
  rcases h2 with ⟨w2, hw2, hw2'⟩
  refine ⟨w1 + w2, hw1.add hw2, ?_⟩
  calc
    (a + c) - (b + d) = (a - b) + (c - d) := by ring
    _ = 2 * w1 + 2 * w2 := by rw [hw1', hw2']
    _ = 2 * (w1 + w2) := by ring

public lemma sub {a b c d : ℂ} (h1 : CongruentModTwo a b) (h2 : CongruentModTwo c d) :
    CongruentModTwo (a - c) (b - d) := by
  rcases h1 with ⟨w1, hw1, hw1'⟩
  rcases h2 with ⟨w2, hw2, hw2'⟩
  refine ⟨w1 - w2, hw1.sub hw2, ?_⟩
  calc
    (a - c) - (b - d) = (a - b) - (c - d) := by ring
    _ = 2 * w1 - 2 * w2 := by rw [hw1', hw2']
    _ = 2 * (w1 - w2) := by ring

public lemma neg {a b : ℂ} (h : CongruentModTwo a b) : CongruentModTwo (-a) (-b) := by
  rcases h with ⟨w, hw, hw'⟩
  refine ⟨-w, hw.neg, ?_⟩
  calc
    (-a) - (-b) = -(a - b) := by ring
    _ = -(2 * w) := by rw [hw']
    _ = 2 * (-w) := by ring

/-- Multiply a congruence by an algebraic integer. -/
public lemma mul_left {a b c : ℂ} (h : CongruentModTwo a b) (hc : IsIntegral ℤ c) :
    CongruentModTwo (a * c) (b * c) := by
  rcases h with ⟨w, hw, hw'⟩
  refine ⟨w * c, hw.mul hc, ?_⟩
  calc
    (a * c) - (b * c) = (a - b) * c := by ring
    _ = (2 * w) * c := by rw [hw']
    _ = 2 * (w * c) := by ring

/-- Multiply a congruence by an algebraic integer on the right. -/
public lemma mul_right {a b c : ℂ} (h : CongruentModTwo a b) (hc : IsIntegral ℤ c) :
    CongruentModTwo (c * a) (c * b) := by
  rcases h with ⟨w, hw, hw'⟩
  refine ⟨c * w, hc.mul hw, ?_⟩
  calc
    (c * a) - (c * b) = c * (a - b) := by ring
    _ = c * (2 * w) := by rw [hw']
    _ = 2 * (c * w) := by ring

/-- `2·w ≡ 0` for an algebraic integer `w`. -/
public lemma two_mul_zero {w : ℂ} (hw : IsIntegral ℤ w) : CongruentModTwo (2 * w) 0 :=
  ⟨w, hw, by ring⟩

/-- `x ≡ 0` and `y` an algebraic integer give `x·y ≡ 0`. -/
public lemma mul_zero_left {x y : ℂ} (h : CongruentModTwo x 0) (hy : IsIntegral ℤ y) :
    CongruentModTwo (x * y) 0 := by
  simpa using mul_left h hy

/-- Multiplying an odd integer into an algebraic integer preserves the
congruence class: `n·c ≡ c` when `n` is odd. -/
public lemma odd_mul_congr {n : ℕ} (hn : Odd n) {c : ℂ} (hc : IsIntegral ℤ c) :
    CongruentModTwo ((n : ℂ) * c) c := by
  rcases hn with ⟨m, rfl⟩
  refine ⟨(m : ℂ) * c, ?_, ?_⟩
  · exact (isIntegral_natCast m).mul hc
  · push_cast
    ring

/-- Sums of terms congruent to zero are congruent to zero. -/
public lemma sum_zero {I : Type*} [Fintype I] {f : I → ℂ}
    (h : ∀ i : I, CongruentModTwo (f i) 0) :
    CongruentModTwo (∑ i : I, f i) 0 := by
  classical
  refine Finset.induction_on Finset.univ ?_ ?_
  · simpa using refl (0 : ℂ)
  · intro i s hi hs
    rw [Finset.sum_insert hi]
    simpa using (h i).add hs

/-- Sums of congruences: `Σ f ≡ Σ g` (mod 2) when `f i ≡ g i` for every `i`. -/
public lemma sum {I : Type*} [Fintype I] {f g : I → ℂ}
    (h : ∀ i : I, CongruentModTwo (f i) (g i)) :
    CongruentModTwo (∑ i : I, f i) (∑ i : I, g i) := by
  classical
  refine Finset.induction_on Finset.univ ?_ ?_
  · simpa using refl (0 : ℂ)
  · intro i s hi hs
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i).add hs

/-- Congruence of equal numbers. -/
public lemma of_eq {a b : ℂ} (h : a = b) : CongruentModTwo a b := by
  rw [h]
  exact refl b

/-- `a ≡ 0` iff `a` is twice an algebraic integer. -/
public lemma iff_exists {a : ℂ} : CongruentModTwo a 0 ↔ ∃ w : ℂ, IsIntegral ℤ w ∧ a = 2 * w := by
  constructor
  · rintro ⟨w, hw, hw'⟩
    exact ⟨w, hw, by simpa using hw'⟩
  · rintro ⟨w, hw, hw'⟩
    exact ⟨w, hw, by rw [hw']; ring⟩

end CongruentModTwo

end CFSG.BenderGlauberman

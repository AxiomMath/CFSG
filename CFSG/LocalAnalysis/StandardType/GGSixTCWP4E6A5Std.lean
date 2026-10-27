module

public import Aesop.BuiltinRules
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.StandardType.TableCRes

@[expose] def ip5 : List ℤ → List ℤ → ℤ
  | [x0, x1, x2, x3, x4], [y0, y1, y2, y3, y4] =>
    2 * (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4) -
      (x0 * y1 + x1 * y0 + x1 * y2 + x2 * y1 + x2 * y3 + x3 * y2 + x3 * y4 + x4 * y3)
  | _, _ => 0

@[expose] def intv (a b : ℕ) : List ℤ := (List.range 5).map fun i => if a ≤ i ∧ i < b then 1 else 0

@[expose] def reflectStd (g v : List ℤ) : List ℤ := List.zipWith (fun x y => x - ip5 g v * y) v g

@[expose] def applyWordStd (w : List (ℕ × ℕ)) (v : List ℤ) : List ℤ :=
  w.foldr (fun ab v => reflectStd (intv ab.1 ab.2) v) v

@[expose] def stdPos : List (List ℤ) :=
  [intv 0 1, intv 0 2, intv 0 3, intv 0 4, intv 0 5, intv 1 2, intv 1 3, intv 1 4, intv 1 5,
    intv 2 3, intv 2 4, intv 2 5, intv 3 4, intv 3 5, intv 4 5]

@[expose] def tcNegS (a : List ℤ) : List ℤ := a.map fun x => -x

@[expose] def std30 : List (List ℤ) := stdPos ++ stdPos.map tcNegS

@[expose] def stdX1 : List (List ℤ) :=
  [intv 0 1, intv 1 2, intv 0 2, tcNegS (intv 0 1), tcNegS (intv 1 2), tcNegS (intv 0 2)]

@[expose] def stdX2 : List (List ℤ) :=
  [intv 3 4, intv 4 5, intv 3 5, tcNegS (intv 3 4), tcNegS (intv 4 5), tcNegS (intv 3 5)]

@[expose] def stdFneg : List (List ℤ) :=
  [tcNegS (intv 0 3), tcNegS (intv 0 4), tcNegS (intv 0 5), tcNegS (intv 1 3), tcNegS (intv 1 4),
    tcNegS (intv 1 5), tcNegS (intv 2 3), tcNegS (intv 2 4), tcNegS (intv 2 5)]

@[expose] def blockSwapWords : List (List (ℕ × ℕ)) := [
  [(2, 5), (1, 4), (0, 3)],
  [(2, 4), (1, 5), (1, 2), (0, 3)],
  [(2, 4), (1, 3), (0, 5), (0, 2), (0, 1)],
  [(2, 5), (1, 3), (0, 4), (0, 1)],
  [(2, 3), (1, 4), (0, 5), (0, 2)],
  [(2, 3), (1, 5), (1, 2), (0, 4), (0, 1)],
  [(2, 5), (1, 4), (0, 3), (0, 2), (0, 1)],
  [(2, 4), (1, 5), (0, 3), (0, 2)],
  [(2, 4), (1, 3), (1, 2), (0, 5), (0, 1)],
  [(2, 5), (1, 3), (1, 2), (0, 4)],
  [(2, 3), (1, 4), (0, 5), (0, 1)],
  [(2, 3), (1, 5), (0, 4)],
  [(2, 5), (1, 4), (1, 2), (0, 3)],
  [(2, 4), (1, 5), (0, 3)],
  [(2, 4), (1, 3), (0, 5), (0, 1)],
  [(2, 5), (1, 3), (0, 4), (0, 2), (0, 1)],
  [(2, 3), (1, 4), (1, 2), (0, 5), (0, 1)],
  [(2, 3), (1, 5), (0, 4), (0, 2)],
  [(2, 5), (1, 4), (0, 3), (0, 1)],
  [(2, 4), (1, 5), (1, 2), (0, 3), (0, 1)],
  [(2, 4), (1, 3), (0, 5), (0, 2)],
  [(2, 5), (1, 3), (0, 4)],
  [(2, 3), (1, 4), (0, 5), (0, 2), (0, 1)],
  [(2, 3), (1, 5), (1, 2), (0, 4)],
  [(2, 5), (1, 4), (0, 3), (0, 2)],
  [(2, 4), (1, 5), (0, 3), (0, 2), (0, 1)],
  [(2, 4), (1, 3), (1, 2), (0, 5)],
  [(2, 5), (1, 3), (1, 2), (0, 4), (0, 1)],
  [(2, 3), (1, 4), (0, 5)],
  [(2, 3), (1, 5), (0, 4), (0, 1)],
  [(2, 5), (1, 4), (1, 2), (0, 3), (0, 1)],
  [(2, 4), (1, 5), (0, 3), (0, 1)],
  [(2, 4), (1, 3), (0, 5)],
  [(2, 5), (1, 3), (0, 4), (0, 2)],
  [(2, 3), (1, 4), (1, 2), (0, 5)],
  [(2, 3), (1, 5), (0, 4), (0, 2), (0, 1)]]

@[expose] def tcWordOK (e₀ e₁ e₂ e₃ e₄ : List ℤ) : Prop :=
  ∃ w ∈ blockSwapWords, applyWordStd w (intv 0 1) = e₀ ∧ applyWordStd w (intv 1 2) = e₁ ∧
    applyWordStd w (intv 2 3) = e₂ ∧ applyWordStd w (intv 3 4) = e₃ ∧
    applyWordStd w (intv 4 5) = e₄

instance (e₀ e₁ e₂ e₃ e₄ : List ℤ) : Decidable (tcWordOK e₀ e₁ e₂ e₃ e₄) := by
  unfold tcWordOK
  infer_instance

@[expose] def Lvl4 (e₀ e₁ e₂ e₃ : List ℤ) : Prop :=
  ∀ e₄ ∈ stdX1, ip5 e₃ e₄ = -1 → ip5 e₂ e₄ = 0 → ip5 e₁ e₄ = 0 → ip5 e₀ e₄ = 0 →
    tcWordOK e₀ e₁ e₂ e₃ e₄

instance (e₀ e₁ e₂ e₃ : List ℤ) : Decidable (Lvl4 e₀ e₁ e₂ e₃) := by
  unfold Lvl4
  infer_instance

@[expose] def Lvl3 (e₀ e₁ e₂ : List ℤ) : Prop :=
  ∀ e₃ ∈ stdX1, ip5 e₂ e₃ = -1 → ip5 e₁ e₃ = 0 → ip5 e₀ e₃ = 0 → Lvl4 e₀ e₁ e₂ e₃

instance (e₀ e₁ e₂ : List ℤ) : Decidable (Lvl3 e₀ e₁ e₂) := by
  unfold Lvl3
  infer_instance

@[expose] def Lvl2 (e₀ e₁ : List ℤ) : Prop :=
  ∀ e₂ ∈ stdFneg, ip5 e₁ e₂ = -1 → ip5 e₀ e₂ = 0 → Lvl3 e₀ e₁ e₂

instance (e₀ e₁ : List ℤ) : Decidable (Lvl2 e₀ e₁) := by
  unfold Lvl2
  infer_instance

theorem std_swap_words :
    ∀ e₀ ∈ stdX2, ∀ e₁ ∈ stdX2, ip5 e₀ e₁ = -1 → Lvl2 e₀ e₁ := by
  decide +kernel

end CFSG.StandardType.TableCRes

end

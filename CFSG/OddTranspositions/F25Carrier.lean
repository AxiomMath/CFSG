module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

public section

namespace CFSG.OddTranspositions.QZ

structure F25t where
  a : ZMod 5
  b : ZMod 5
deriving DecidableEq, Repr

@[ext] theorem F25t.ext {x y : F25t} (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x; cases y; simp_all

instance : Fintype F25t where
  elems := ((Finset.univ : Finset (ZMod 5)).product (Finset.univ)).image
    (fun p => (⟨p.1, p.2⟩ : F25t))
  complete := fun x =>
    Finset.mem_image.mpr
      ⟨(x.a, x.b), Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩

instance : Zero F25t := ⟨⟨0, 0⟩⟩
instance : One F25t := ⟨⟨1, 0⟩⟩
instance : Add F25t := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg F25t := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Mul F25t := ⟨fun x y => ⟨x.a * y.a + 3 * x.b * y.b, x.a * y.b + x.b * y.a⟩⟩
instance : Inv F25t :=
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  ⟨fun x =>
    ⟨x.a / (x.a ^ 2 - 3 * x.b ^ 2), -x.b / (x.a ^ 2 - 3 * x.b ^ 2)⟩⟩

theorem hns25 : ¬ IsSquare (3 : ZMod 5) := by
  rintro ⟨b, hb⟩
  have h : ∀ b : ZMod 5, b ^ 2 ≠ 3 := by decide
  exact h b (by simpa [pow_two] using hb.symm)

theorem norm_ne_zero {x : F25t} (hx : x ≠ 0) : x.a ^ 2 - 3 * x.b ^ 2 ≠ 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro hn
  have hxab : x.a ^ 2 = 3 * x.b ^ 2 := sub_eq_zero.mp hn
  by_cases hb : x.b = 0
  · have ha : x.a = 0 := by
      have h0 : x.a ^ 2 = 0 := by simpa [hb] using hxab
      exact pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp h0
    apply hx
    ext
    · rw [ha]; rfl
    · rw [hb]; rfl
  · apply hns25
    refine ⟨x.a / x.b, ?_⟩
    field_simp [hb]
    exact hxab.symm

theorem card_F25t : Fintype.card F25t = 25 := by
  decide

end CFSG.OddTranspositions.QZ

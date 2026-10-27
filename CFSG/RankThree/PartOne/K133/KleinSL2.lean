module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartOne.K133

open Matrix CFSG

variable {F : Type*} [Field F]

@[expose] def tSL (a : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem tSL_mul (a b : F) : tSL a * tSL b = tSL (a + b) := by
  apply Subtype.ext
  show (!![1, a; 0, 1] * !![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) F) = !![1, a + b; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem tSL_zero : tSL (0 : F) = 1 := by
  apply Subtype.ext
  simp only [tSL, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem tSL_injective : Function.Injective (tSL : F → SpecialLinearGroup (Fin 2) F) := by
  intro a b h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [tSL] using this

@[expose] def tHom (F : Type*) [Field F] : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun a := tSL a.toAdd
  map_one' := by simp [tSL_zero]
  map_mul' a b := by simp [tSL_mul]

theorem tHom_injective : Function.Injective (tHom F) := fun a b h => by
  have := tSL_injective h
  exact Multiplicative.toAdd.injective this

theorem exists_klein_four_sl2 [Finite F] [CharP F 2] {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card F = 2 ^ f) :
    ∃ V : Subgroup (SpecialLinearGroup (Fin 2) F), IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  classical
  have hdvd : 2 ^ 2 ∣ Nat.card (Multiplicative F) := by
    rw [Nat.card_congr Multiplicative.toAdd, hcard]
    exact pow_dvd_pow 2 hf
  obtain ⟨V', hV'⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  refine ⟨V'.map (tHom F), ?_, ?_⟩
  · refine
      { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_ }
    · obtain ⟨a, ha, hax⟩ := x.2
      obtain ⟨b, hb, hby⟩ := y.2
      apply Subtype.ext
      show (x : SpecialLinearGroup (Fin 2) F) * y = y * x
      rw [← hax, ← hby, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨a, ha, hax⟩ := x.2
      apply Subtype.ext
      show (x : SpecialLinearGroup (Fin 2) F) ^ 2 = 1
      rw [← hax, ← map_pow, sq]
      have : a * a = 1 := by
        apply Multiplicative.toAdd.injective
        simp [toAdd_mul, CharTwo.add_self_eq_zero]
      rw [this, map_one]
  · rw [Subgroup.card_map_of_injective tHom_injective, hV']
    norm_num

end CFSG.RankThree.PartOne.K133

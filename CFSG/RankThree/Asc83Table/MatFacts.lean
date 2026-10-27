module

public import CFSG.RankThree.Asc83Table.MatCertDefs
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.Asc83Table

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

variable {p d : ℕ}

@[expose] def slpInit (A B : Matrix (Fin d) (Fin d) (ZMod p)) : ℕ → Matrix (Fin d) (Fin d) (ZMod p) :=
  fun r => if r = 0 then A else if r = 1 then B else 1

@[expose] def slpStep (R : ℕ → Matrix (Fin d) (Fin d) (ZMod p)) :
    Op → ℕ → Matrix (Fin d) (Fin d) (ZMod p)
  | .mul i j k => Function.update R k (R i * R j)
  | .pow e i k => Function.update R k (R i ^ e)

@[expose] def slpRegs (A B : Matrix (Fin d) (Fin d) (ZMod p)) (prog : List Op) :
    ℕ → Matrix (Fin d) (Fin d) (ZMod p) :=
  prog.foldl slpStep (slpInit A B)

@[expose] def wordProd (R : ℕ → Matrix (Fin d) (Fin d) (ZMod p)) (w : Word) :
    Matrix (Fin d) (Fin d) (ZMod p) :=
  (w.map fun q => R q.1 ^ q.2).prod

@[expose] def Native.MFact.Holds (R : ℕ → Matrix (Fin d) (Fin d) (ZMod p)) (n : ℕ) : MFact → Prop
  | .ord r e => r < n ∧ 0 < e ∧ R r ^ e = 1
  | .conj h u w => h < n ∧ wordLt n u = true ∧ wordLt n w = true ∧
      R h * wordProd R u = wordProd R w * R h
  | .ne w₁ w₂ t => wordLt n w₁ = true ∧ wordLt n w₂ = true ∧
      ∃ ht : t < d, wordProd R w₁ ⟨t, ht⟩ ≠ wordProd R w₂ ⟨t, ht⟩
  | .eq w₁ w₂ => wordLt n w₁ = true ∧ wordLt n w₂ = true ∧ wordProd R w₁ = wordProd R w₂

theorem wordProd_congr {R R' : ℕ → Matrix (Fin d) (Fin d) (ZMod p)} {n : ℕ}
    (h : ∀ r < n, R r = R' r) : ∀ {w : Word}, wordLt n w = true → wordProd R w = wordProd R' w
  | [], _ => rfl
  | (r, e) :: w, hw => by
    simp only [wordLt, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    have := wordProd_congr h (w := w) hw.2
    simp only [wordProd, List.map_cons, List.prod_cons] at this ⊢
    rw [h r hw.1, this]

theorem Native.MFact.Holds.congr {R R' : ℕ → Matrix (Fin d) (Fin d) (ZMod p)} {n : ℕ}
    (h : ∀ r < n, R r = R' r) {f : MFact} (hf : f.Holds R n) : f.Holds R' n := by
  cases f with
  | ord r e => exact ⟨hf.1, hf.2.1, h r hf.1 ▸ hf.2.2⟩
  | conj g u w =>
    obtain ⟨hg, hu, hw, e⟩ := hf
    exact ⟨hg, hu, hw, by rw [← h g hg, ← wordProd_congr h hu, ← wordProd_congr h hw]; exact e⟩
  | ne w₁ w₂ t =>
    obtain ⟨h₁, h₂, ht, e⟩ := hf
    exact ⟨h₁, h₂, ht, by rw [← wordProd_congr h h₁, ← wordProd_congr h h₂]; exact e⟩
  | eq w₁ w₂ =>
    obtain ⟨h₁, h₂, e⟩ := hf
    exact ⟨h₁, h₂, by rw [← wordProd_congr h h₁, ← wordProd_congr h h₂]; exact e⟩

end CFSG.RankThree.Asc83Table

end

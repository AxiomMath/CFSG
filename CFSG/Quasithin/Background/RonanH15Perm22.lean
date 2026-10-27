module

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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.RonanH15

theorem perm_pair_iff_22 {a b j : Fin 24} (hab : a ≠ b) (hja : j ≠ a) (hjb : j ≠ b)
    {g : Equiv.Perm (Fin 24)} (hg : (g a = a ∧ g b = b) ∨ (g a = b ∧ g b = a)) :
    (({a, j} : Finset (Fin 24)) = {g a, g j} ∨
        symmDiff ({a, j} : Finset (Fin 24)) {g a, g j} = {a, b}) ↔ g j = j := by
  have hba : b ≠ a := Ne.symm hab
  have hja' : a ≠ j := Ne.symm hja
  have hjb' : b ≠ j := Ne.symm hjb
  rcases hg with ⟨ha, hb⟩ | ⟨ha, hb⟩
  ·
    have hgja : g j ≠ a := fun h => hja (g.injective (h.trans ha.symm))
    have hgjb : g j ≠ b := fun h => hjb (g.injective (h.trans hb.symm))
    rw [ha]
    by_cases hgj : g j = j
    · simp [hgj]
    · have hgj' : j ≠ g j := Ne.symm hgj
      constructor
      · rintro (h | h)
        · exfalso
          have hj := Finset.ext_iff.1 h j
          simp [hja, hgj'] at hj
        · exfalso
          have hb' := Finset.ext_iff.1 h b
          simp [Finset.mem_symmDiff, hba, hjb', Ne.symm hgjb] at hb'
      · intro h
        exact absurd h hgj
  ·
    have hgja : g j ≠ a := fun h => hjb (g.injective (h.trans hb.symm))
    have hgjb : g j ≠ b := fun h => hja (g.injective (h.trans ha.symm))
    rw [ha]
    by_cases hgj : g j = j
    · rw [hgj]
      have key : symmDiff ({a, j} : Finset (Fin 24)) {b, j} = {a, b} := by
        ext x
        by_cases h1 : x = a
        · subst h1
          simp [Finset.mem_symmDiff, hab, hja', hjb', Ne.symm hab]
        · by_cases h2 : x = b
          · subst h2
            simp [Finset.mem_symmDiff, hba, hjb', h1]
          · by_cases h3 : x = j
            · subst h3
              simp [Finset.mem_symmDiff, hja, hjb, h1, h2]
            · simp [Finset.mem_symmDiff, h1, h2, h3]
      exact iff_of_true (Or.inr key) rfl
    · have hgj' : j ≠ g j := Ne.symm hgj
      constructor
      · rintro (h | h)
        · exfalso
          have ha' := Finset.ext_iff.1 h a
          simp [hab, Ne.symm hgja] at ha'
        · exfalso
          have hj := Finset.ext_iff.1 h j
          simp [Finset.mem_symmDiff, hja, hjb, hgj'] at hj
      · intro h
        exact absurd h hgj

theorem exists_ne_pair (a b : Fin 24) : ∃ j : Fin 24, j ≠ a ∧ j ≠ b := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin 24)) ⊆ {a, b} := by
    intro x _
    by_cases hx : x = a
    · simp [hx]
    · simp [h x hx]
  have h1 := Finset.card_le_card hsub
  have h2 : ({a, b} : Finset (Fin 24)).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem symmDiff_pair_swap {a b j : Fin 24} (hab : a ≠ b) (hja : j ≠ a) (hjb : j ≠ b) :
    symmDiff ({b, j} : Finset (Fin 24)) {a, j} = {a, b} := by
  have hba : b ≠ a := Ne.symm hab
  have hja' : a ≠ j := Ne.symm hja
  have hjb' : b ≠ j := Ne.symm hjb
  ext x
  by_cases h1 : x = a
  · subst h1
    simp [Finset.mem_symmDiff, hab, hja', hjb', hba]
  · by_cases h2 : x = b
    · subst h2
      simp [Finset.mem_symmDiff, hba, hjb', h1]
    · by_cases h3 : x = j
      · subst h3
        simp [Finset.mem_symmDiff, hja, hjb, h1, h2]
      · simp [Finset.mem_symmDiff, h1, h2, h3]

end CFSG.Quasithin.RonanH15

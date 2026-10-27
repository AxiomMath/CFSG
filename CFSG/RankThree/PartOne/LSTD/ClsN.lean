module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartOne.LSTD

abbrev A5 {α : Type} (u : Fin 5 → α) : Prop :=
  u 0 = u 1 ∧ u 1 = u 2 ∧ u 3 ≠ u 0 ∧ u 4 ≠ u 0 ∧ u 3 ≠ u 4

abbrev B5 {α : Type} (u : Fin 5 → α) : Prop :=
  u 0 ≠ u 2 ∧ u 0 ≠ u 3 ∧ u 0 ≠ u 4 ∧ u 1 ≠ u 2 ∧ u 1 ≠ u 3 ∧ u 1 ≠ u 4 ∧ u 2 ≠ u 4 ∧ u 3 ≠ u 4

def sortedWitness (a b c d e : Fin 5) : Fin 5 → Fin 5 :=
  if a = b ∧ b = c then ![0, 1, 2, 3, 4]
  else if b = c ∧ c = d then ![1, 2, 3, 0, 4]
  else if c = d ∧ d = e then ![2, 3, 4, 0, 1]
  else if b = c ∧ d = e then ![1, 2, 3, 4, 0]
  else if a = b ∧ d = e then ![0, 1, 3, 4, 2]
  else if a = b ∧ c = d then ![0, 1, 2, 3, 4]
  else if b = c then ![1, 2, 3, 4, 0]
  else if c = d then ![2, 3, 0, 1, 4]
  else if d = e then ![3, 4, 0, 1, 2]
  else ![0, 1, 2, 3, 4]

theorem sorted_cases : ∀ a b c d e : Fin 5, a ≤ b → b ≤ c → c ≤ d → d ≤ e →
    (a.val + b.val + c.val + d.val + e.val) % 5 = 0 → a ≠ e →
    Function.Injective (sortedWitness a b c d e) ∧
      (A5 (fun i => ![a, b, c, d, e] (sortedWitness a b c d e i)) ∨
        B5 (fun i => ![a, b, c, d, e] (sortedWitness a b c d e i))) := by
  decide

theorem exists_perm_cases (m : Fin 5 → Fin 5) (hsum : (∑ i, (m i : ℕ)) % 5 = 0)
    (hnc : ∃ i j, m i ≠ m j) :
    ∃ ρ : Equiv.Perm (Fin 5), A5 (fun i => m (ρ i)) ∨ B5 (fun i => m (ρ i)) := by
  set σ := Tuple.sort m with hσ
  have hmono : Monotone (m ∘ σ) := Tuple.monotone_sort m
  have hle : ∀ i j : Fin 5, i ≤ j → m (σ i) ≤ m (σ j) := fun i j hij => hmono hij
  have hsum' : ((m (σ 0)).val + (m (σ 1)).val + (m (σ 2)).val + (m (σ 3)).val +
      (m (σ 4)).val) % 5 = 0 := by
    have h1 : ∑ i, (m (σ i) : ℕ) = ∑ i, (m i : ℕ) := Equiv.sum_comp σ (fun i => (m i : ℕ))
    rw [Fin.sum_univ_five] at h1
    omega
  have hae : m (σ 0) ≠ m (σ 4) := by
    intro h
    obtain ⟨i, j, hij⟩ := hnc
    have hall : ∀ k : Fin 5, m k = m (σ 0) := by
      intro k
      obtain ⟨l, rfl⟩ := σ.surjective k
      exact le_antisymm (h ▸ hle l 4 (Fin.le_last l)) (hle 0 l (Fin.zero_le l))
    exact hij ((hall i).trans (hall j).symm)
  obtain ⟨hinj, hcase⟩ := sorted_cases (m (σ 0)) (m (σ 1)) (m (σ 2)) (m (σ 3)) (m (σ 4))
    (hle 0 1 (by decide)) (hle 1 2 (by decide)) (hle 2 3 (by decide)) (hle 3 4 (by decide))
    hsum' hae
  have hρ : Function.Injective (fun i => σ (sortedWitness (m (σ 0)) (m (σ 1)) (m (σ 2))
      (m (σ 3)) (m (σ 4)) i)) := σ.injective.comp hinj
  refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hρ), ?_⟩
  have hmt : ∀ i, m (σ (sortedWitness (m (σ 0)) (m (σ 1)) (m (σ 2)) (m (σ 3)) (m (σ 4)) i)) =
      ![m (σ 0), m (σ 1), m (σ 2), m (σ 3), m (σ 4)]
        (sortedWitness (m (σ 0)) (m (σ 1)) (m (σ 2)) (m (σ 3)) (m (σ 4)) i) := by
    intro i
    generalize sortedWitness (m (σ 0)) (m (σ 1)) (m (σ 2)) (m (σ 3)) (m (σ 4)) i = k
    fin_cases k <;> rfl
  simpa [A5, B5, hmt] using hcase

section Units

variable {K : Type} [Field K]

theorem exists_pow_lt_five {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 5) {u : Kˣ} (hu : u ^ 5 = 1) :
    ∃ m < 5, ζ ^ m = u := by
  have hζK : IsPrimitiveRoot (ζ : K) 5 := IsPrimitiveRoot.coe_units_iff.mpr hζ
  have hu' : (u : K) ^ 5 = 1 := by
    have := congrArg (fun w : Kˣ => (w : K)) hu
    simpa using this
  obtain ⟨m, hm, hmu⟩ := hζK.eq_pow_of_pow_eq_one hu'
  exact ⟨m, hm, Units.ext (by simpa using hmu)⟩

theorem exists_perm_cases_units {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 5) (v : Fin 5 → Kˣ)
    (hv5 : ∀ i, v i ^ 5 = 1) (hprod : ∏ i, v i = 1) (hnc : ∃ i j, v i ≠ v j) :
    ∃ ρ : Equiv.Perm (Fin 5), A5 (fun i => v (ρ i)) ∨ B5 (fun i => v (ρ i)) := by
  have hex : ∀ i, ∃ k : Fin 5, ζ ^ (k : ℕ) = v i := fun i => by
    obtain ⟨k, hk, hkv⟩ := exists_pow_lt_five hζ (hv5 i)
    exact ⟨⟨k, hk⟩, hkv⟩
  choose m hm using hex
  have hinj : ∀ i j, v i = v j ↔ m i = m j := fun i j => by
    constructor
    · intro h
      exact Fin.ext (hζ.pow_inj (m i).2 (m j).2 ((hm i).trans (h.trans (hm j).symm)))
    · intro h
      rw [← hm i, ← hm j, h]
  have hsum : (∑ i, (m i : ℕ)) % 5 = 0 := by
    have h1 : ζ ^ (∑ i, (m i : ℕ)) = 1 := by
      rw [← Finset.prod_pow_eq_pow_sum]
      simp only [hm]
      exact hprod
    exact Nat.mod_eq_zero_of_dvd ((hζ.pow_eq_one_iff_dvd _).mp h1)
  obtain ⟨i, j, hij⟩ := hnc
  obtain ⟨ρ, hρ⟩ := exists_perm_cases m hsum ⟨i, j, fun h => hij ((hinj i j).mpr h)⟩
  refine ⟨ρ, ?_⟩
  simpa only [A5, B5, ne_eq, hinj] using hρ

end Units

end CFSG.RankThree.PartOne.LSTD

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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.RonanG25

section Defs

variable {G : Type} [Group G]

structure IsOpCompSeries (X P : Subgroup G) (k : ℕ) (Ps : ℕ → Subgroup G) : Prop where
  zero : Ps 0 = ⊥
  top : Ps k = P
  mono : ∀ i < k, Ps i ≤ Ps (i + 1)
  strict : ∀ i < k, Ps i < Ps (i + 1)
  inv : ∀ i ≤ k, ∀ x ∈ X, ∀ y ∈ Ps i, x * y * x⁻¹ ∈ Ps i
  normal : ∀ i < k, ∀ y ∈ Ps (i + 1), ∀ z ∈ Ps i, y * z * y⁻¹ ∈ Ps i
  simple : ∀ i < k, ∀ Q : Subgroup G, Ps i ≤ Q → Q ≤ Ps (i + 1) →
    (∀ x ∈ X, ∀ y ∈ Q, x * y * x⁻¹ ∈ Q) → (∀ y ∈ Ps (i + 1), ∀ z ∈ Q, y * z * y⁻¹ ∈ Q) →
      Q = Ps i ∨ Q = Ps (i + 1)

@[expose] def FactorCentral (X A B : Subgroup G) : Prop :=
  ∀ x ∈ X, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ A

@[expose] def FactorNatural (F : Type) [Field F] (X A B : Subgroup G) : Prop :=
  ∃ (φ : ↥B →* Multiplicative (Fin 2 → F)) (β : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F),
    Function.Surjective φ ∧ (∀ y : ↥B, φ y = 1 ↔ (y : G) ∈ A) ∧
    (∀ (x : ↥X) (y y' : ↥B), (x : G) * (y : G) * (x : G)⁻¹ = (y' : G) →
      Multiplicative.toAdd (φ y') =
        ((β x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
          (Multiplicative.toAdd (φ y))) ∧
    (Nat.card F = 2 → β ≠ 1) ∧
    (2 < Nat.card F → ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, ∃ x : ↥X,
      ((β x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (M : Matrix (Fin 2) (Fin 2) F))

open Classical in
@[expose] def HasChiefCounts (F : Type) [Field F] (X P : Subgroup G) (a b : ℕ) : Prop :=
  ∃ (k : ℕ) (Ps : ℕ → Subgroup G), IsOpCompSeries X P k Ps ∧
    (Finset.univ.filter (fun i : Fin k => FactorNatural F X (Ps (i : ℕ)) (Ps ((i : ℕ) + 1)))).card = a ∧
    (Finset.univ.filter (fun i : Fin k =>
      ¬ FactorCentral X (Ps (i : ℕ)) (Ps ((i : ℕ) + 1)) ∧
        ¬ FactorNatural F X (Ps (i : ℕ)) (Ps ((i : ℕ) + 1)))).card = b ∧
    ∀ i : Fin k, ¬ FactorCentral X (Ps (i : ℕ)) (Ps ((i : ℕ) + 1)) →
      ¬ FactorNatural F X (Ps (i : ℕ)) (Ps ((i : ℕ) + 1)) →
        Nat.card ↥(Ps ((i : ℕ) + 1)) = Nat.card F * Nat.card ↥(Ps (i : ℕ))

@[expose] def FactorTwo (A B : Subgroup G) : Prop :=
  ∃ dimension : ℕ, 0 < dimension ∧ Nat.card ↥B = 2 ^ dimension * Nat.card ↥A

open Classical in
@[expose] def HasOrdinaryTwoChiefCounts (F : Type) [Field F] (X : Subgroup G)
    (naturalCount additionalCount : ℕ) : Prop :=
  ∃ (length : ℕ) (terms : ℕ → Subgroup G), IsOpCompSeries X X length terms ∧
    (Finset.univ.filter (fun index : Fin length =>
      FactorTwo (terms (index : ℕ)) (terms ((index : ℕ) + 1)) ∧
        FactorNatural F X (terms (index : ℕ)) (terms ((index : ℕ) + 1)))).card = naturalCount ∧
    (Finset.univ.filter (fun index : Fin length =>
      FactorTwo (terms (index : ℕ)) (terms ((index : ℕ) + 1)) ∧
        ¬ FactorCentral X (terms (index : ℕ)) (terms ((index : ℕ) + 1)) ∧
        ¬ FactorNatural F X (terms (index : ℕ)) (terms ((index : ℕ) + 1)))).card = additionalCount ∧
    ∀ index : Fin length,
      FactorTwo (terms (index : ℕ)) (terms ((index : ℕ) + 1)) →
      ¬ FactorCentral X (terms (index : ℕ)) (terms ((index : ℕ) + 1)) →
      ¬ FactorNatural F X (terms (index : ℕ)) (terms ((index : ℕ) + 1)) →
        Nat.card ↥(terms ((index : ℕ) + 1)) = Nat.card F * Nat.card ↥(terms (index : ℕ))

end Defs

section Chain

variable {G : Type} [Group G]

@[expose] def Inv (X A : Subgroup G) : Prop := ∀ x ∈ X, ∀ y ∈ A, x * y * x⁻¹ ∈ A

structure ChiefStep (X A B : Subgroup G) : Prop where
  lt : A < B
  invA : Inv X A
  invB : Inv X B
  normal : ∀ y ∈ B, ∀ z ∈ A, y * z * y⁻¹ ∈ A
  simple : ∀ Q : Subgroup G, A ≤ Q → Q ≤ B → Inv X Q → (∀ y ∈ B, ∀ z ∈ Q, y * z * y⁻¹ ∈ Q) →
    Q = A ∨ Q = B

inductive ChainCounts (F : Type) [Field F] (X : Subgroup G) (ord : Bool) :
    Subgroup G → Subgroup G → ℕ → ℕ → Prop
  | refl (A : Subgroup G) (hA : Inv X A) : ChainCounts F X ord A A 0 0
  | natural {A B C : Subgroup G} {a b : ℕ} (hs : ChiefStep X A B) (hn : FactorNatural F X A B)
      (rest : ChainCounts F X ord B C a b) : ChainCounts F X ord A C (a + 1) b
  | additional {A B C : Subgroup G} {a b : ℕ} (hs : ChiefStep X A B)
      (habel : ∀ y ∈ B, ∀ z ∈ B, y * z * y⁻¹ * z⁻¹ ∈ A)
      (hc : ¬ FactorCentral X A B) (hcard : Nat.card B = Nat.card F * Nat.card A)
      (rest : ChainCounts F X ord B C a b) : ChainCounts F X ord A C a (b + 1)
  | central {A B C : Subgroup G} {a b : ℕ} (hs : ChiefStep X A B) (hc : FactorCentral X A B)
      {p : ℕ} (hp : p.Prime) (hcard : Nat.card B = p * Nat.card A)
      (rest : ChainCounts F X ord B C a b) : ChainCounts F X ord A C a b
  | other {A B C : Subgroup G} {a b : ℕ} (hord : ord = true) (hs : ChiefStep X A B)
      (h2 : ¬ FactorTwo A B) (rest : ChainCounts F X ord B C a b) : ChainCounts F X ord A C a b

variable {F : Type} [Field F] {X : Subgroup G} {ord : Bool}

theorem ChainCounts.le {A C : Subgroup G} {a b : ℕ} (h : ChainCounts F X ord A C a b) :
    A ≤ C := by
  induction h with
  | refl A hA => exact le_rfl
  | natural hs hn rest ih => exact hs.lt.le.trans ih
  | additional hs habel hc hcard rest ih => exact hs.lt.le.trans ih
  | central hs hc hp hcard rest ih => exact hs.lt.le.trans ih
  | other hord hs h2 rest ih => exact hs.lt.le.trans ih

theorem ChainCounts.invRight {A C : Subgroup G} {a b : ℕ} (h : ChainCounts F X ord A C a b) :
    Inv X C := by
  induction h with
  | refl A hA => exact hA
  | natural hs hn rest ih => exact ih
  | additional hs habel hc hcard rest ih => exact ih
  | central hs hc hp hcard rest ih => exact ih
  | other hord hs h2 rest ih => exact ih

theorem FactorNatural.not_central {F : Type} [Field F] [Finite F] {X A B : Subgroup G}
    (hAB : A ≤ B)
    (h : FactorNatural F X A B) : ¬ FactorCentral X A B := by
  intro hc
  obtain ⟨φ, β, hφs, hφk, hφe, h2, h3⟩ := h
  have hfix : ∀ (x : ↥X) (w : Fin 2 → F),
      ((β x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec w = w := by
    intro x w
    obtain ⟨y, hy⟩ := hφs (Multiplicative.ofAdd w)
    have hcm : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ A := hc x x.2 y y.2
    have hmem : (x : G) * (y : G) * (x : G)⁻¹ ∈ B := by
      have : (x : G) * (y : G) * (x : G)⁻¹ =
          ((x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹) * (y : G) := by group
      rw [this]
      exact B.mul_mem (hAB hcm) y.2
    have hker : φ ⟨(x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹, B.mul_mem hmem (B.inv_mem y.2)⟩ = 1 :=
      (hφk _).2 hcm
    have hy' : φ ⟨(x : G) * (y : G) * (x : G)⁻¹, hmem⟩ = φ y := by
      have : (⟨(x : G) * (y : G) * (x : G)⁻¹, hmem⟩ : ↥B) =
          ⟨(x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹, B.mul_mem hmem (B.inv_mem y.2)⟩ * y :=
        Subtype.ext (by simp)
      rw [this, map_mul, hker, one_mul]
    have := hφe x y ⟨(x : G) * (y : G) * (x : G)⁻¹, hmem⟩ rfl
    rw [hy', hy] at this
    simpa using this.symm
  have hone : ∀ x : ↥X, (β x : Matrix.GeneralLinearGroup (Fin 2) F) = 1 := by
    intro x
    refine Units.ext (Matrix.ext fun i j => ?_)
    have := hfix x (Pi.single j 1)
    have h' := congrFun this i
    simp only [Matrix.mulVec_single_one] at h'
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h'
  by_cases hF : Nat.card F = 2
  · exact h2 hF (MonoidHom.ext fun x => by simpa using hone x)
  · have h2lt : 2 < Nat.card F := by
      have : 1 < Nat.card F := Finite.one_lt_card
      omega
    obtain ⟨x, hx⟩ := h3 h2lt ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    have := hfix x ![0, 1]
    rw [hx] at this
    have h1 := congrFun this 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1

end Chain

end CFSG.Quasithin.RonanG25

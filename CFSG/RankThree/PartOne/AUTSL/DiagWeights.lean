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
public import Mathlib.LinearAlgebra.Matrix.IsDiag
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

namespace CFSG.RankThree.PartOne.AUTSL

open scoped _root_.Classical

section Support

variable {K : Type*} [Field K] [Fintype K] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def suppSet (I : Finset ι) : Finset (ι → K) :=
  Fintype.piFinset fun i => if i ∈ I then (Finset.univ : Finset K) else {0}

theorem mem_suppSet {I : Finset ι} {v : ι → K} : v ∈ suppSet I ↔ ∀ i, i ∉ I → v i = 0 := by
  unfold suppSet
  rw [Fintype.mem_piFinset]
  refine forall_congr' fun i => ?_
  by_cases hi : i ∈ I
  · simp [hi]
  · simp [hi]

theorem card_suppSet (I : Finset ι) : (suppSet (K := K) I).card = Fintype.card K ^ I.card := by
  unfold suppSet
  rw [Fintype.card_piFinset]
  have : ∀ i, (if i ∈ I then (Finset.univ : Finset K) else {0}).card =
      if i ∈ I then Fintype.card K else 1 := by
    intro i
    by_cases hi : i ∈ I <;> simp [hi]
  simp only [this]
  rw [Finset.prod_ite]
  simp

end Support

section Semilinear

variable {K : Type*} [Field K] [Finite K] {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Type*}

theorem card_le_of_semilinear (d d' : B → Matrix ι ι K) (hd : ∀ b, (d b).IsDiag)
    (hd' : ∀ b, (d' b).IsDiag) (σ : K →+* K)
    (A : Matrix ι ι K) (hA : IsUnit A) (θ : B → B) (hθ : Function.Surjective θ)
    (hΘ : ∀ b, A * (d b).map σ = d' (θ b) * A) (χ χ' : B → K)
    (hχχ' : ∀ b, χ' (θ b) = σ (χ b)) :
    (Finset.univ.filter fun i : ι => ∀ b, d b i i = χ b).card ≤
      (Finset.univ.filter fun i : ι => ∀ b, d' b i i = χ' b).card := by
  have : Fintype K := Fintype.ofFinite K
  set I := Finset.univ.filter fun i : ι => ∀ b, d b i i = χ b with hI
  set I' := Finset.univ.filter fun i : ι => ∀ b, d' b i i = χ' b with hI'
  let Θ : (ι → K) → (ι → K) := fun v => A.mulVec (fun i => σ (v i))
  have hΘinj : Function.Injective Θ := by
    intro v w h
    obtain ⟨C, hC⟩ : ∃ C : Matrix ι ι K, C * A = 1 := by
      obtain ⟨u, rfl⟩ := hA
      exact ⟨((u⁻¹ : (Matrix ι ι K)ˣ) : Matrix ι ι K), by simp⟩
    have h1 := congrArg (fun x => C.mulVec x) h
    simp only [Θ, Matrix.mulVec_mulVec, hC, Matrix.one_mulVec] at h1
    funext i
    exact σ.injective (congrFun h1 i)
  have hmaps : ∀ v ∈ suppSet (K := K) I, Θ v ∈ suppSet (K := K) I' := by
    intro v hv
    rw [mem_suppSet] at hv ⊢
    have hev : ∀ b, (d b).mulVec v = χ b • v := by
      intro b
      funext i
      have hdiag := hd b
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
      · by_cases hi : i ∈ I
        · have := (Finset.mem_filter.mp hi).2 b
          simp [this]
        · simp [hv i hi]
      · intro j _ hji
        rw [hdiag (Ne.symm hji)]
        simp
      · intro h
        exact absurd (Finset.mem_univ i) h
    intro i hi
    by_contra hne
    apply hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, fun b' => ?_⟩
    obtain ⟨b, rfl⟩ := hθ b'
    have h1 : (d' (θ b)).mulVec (Θ v) = σ (χ b) • Θ v := by
      have e2 : ((d b).map σ).mulVec (fun j => σ (v j)) = fun j => σ (((d b).mulVec v) j) := by
        funext j
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      calc (d' (θ b)).mulVec (Θ v) = (d' (θ b) * A).mulVec (fun j => σ (v j)) := by
              simp only [Θ, Matrix.mulVec_mulVec]
        _ = (A * (d b).map σ).mulVec (fun j => σ (v j)) := by rw [← hΘ b]
        _ = A.mulVec (((d b).map σ).mulVec (fun j => σ (v j))) := by
              rw [← Matrix.mulVec_mulVec]
        _ = A.mulVec (fun j => σ (((d b).mulVec v) j)) := by rw [e2]
        _ = A.mulVec (σ (χ b) • fun j => σ (v j)) := by
              rw [hev b]
              congr 1
              funext j
              simp [map_mul]
        _ = σ (χ b) • Θ v := by rw [Matrix.mulVec_smul]
    have h2 := congrFun h1 i
    have hdiag := hd' (θ b)
    have h3 : ((d' (θ b)).mulVec (Θ v)) i = (d' (θ b)) i i * (Θ v) i := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
      · intro j _ hji
        rw [hdiag (Ne.symm hji)]
        simp
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [h3, Pi.smul_apply, smul_eq_mul] at h2
    rw [hχχ' b]
    exact mul_right_cancel₀ hne h2
  have hcard : (suppSet (K := K) I).card ≤ (suppSet (K := K) I').card := by
    refine Finset.card_le_card_of_injOn Θ (fun v hv => hmaps v hv) (hΘinj.injOn)
  rw [card_suppSet, card_suppSet] at hcard
  have hK : 1 < Fintype.card K := Fintype.one_lt_card
  convert (Nat.pow_le_pow_iff_right hK).mp hcard

end Semilinear

end CFSG.RankThree.PartOne.AUTSL

module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Monster.B.Generic

open Matrix Finset

section Level

variable {V : Type*} [Fintype V] (X : SimpleGraph V) [DecidableRel X.Adj]

theorem sum_adjMatrix_apply {k : ℕ} (hreg : X.IsRegularOfDegree k) (j : V) :
    ∑ i, X.adjMatrix ℝ i j = k := by
  have h := X.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) hreg (a := 1) (v := j)
  rw [mul_one] at h
  rw [← h, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Function.const_apply, mul_one]
  exact (X.isSymm_adjMatrix (α := ℝ)).apply j i

theorem sum_eq_zero_of_eigen {k : ℕ} (hreg : X.IsRegularOfDegree k) {μ : ℝ} {x : V → ℝ}
    (hx : X.adjMatrix ℝ *ᵥ x = μ • x) (hμ : μ ≠ k) : ∑ j, x j = 0 := by
  have h1 : ∑ i, (X.adjMatrix ℝ *ᵥ x) i = k * ∑ j, x j := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, sum_adjMatrix_apply X hreg j]
  have h2 : ∑ i, (X.adjMatrix ℝ *ᵥ x) i = μ * ∑ j, x j := by
    rw [hx, Finset.mul_sum]
    rfl
  have h3 : (μ - k) * ∑ j, x j = 0 := by
    rw [sub_mul, ← h1, ← h2, sub_self]
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (sub_eq_zero.1 h) hμ
  · exact h

theorem dotProduct_self_pos {x : V → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  have h0 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  rcases h0.lt_or_eq with h | h
  · exact h
  · exact absurd (dotProduct_self_eq_zero.1 h.symm) hx

variable [DecidableEq V]

@[expose] def levelMat (α β : ℝ) : Matrix V V ℝ :=
  Matrix.of fun x y => if x = y then 1 else if X.Adj x y then α else β

theorem levelMat_mulVec_apply (α β : ℝ) (x : V → ℝ) (i : V) :
    (levelMat X α β *ᵥ x) i =
      (1 - β) * x i + (α - β) * (X.adjMatrix ℝ *ᵥ x) i + β * ∑ j, x j := by
  have h : ∀ j, levelMat X α β i j * x j =
      (1 - β) * (if i = j then x j else 0) + (α - β) * (X.adjMatrix ℝ i j * x j) +
        β * x j := by
    intro j
    simp only [levelMat, Matrix.of_apply, SimpleGraph.adjMatrix_apply]
    by_cases hij : i = j
    · subst hij
      simp only [ite_true, X.irrefl, ite_false]
      ring
    · by_cases ha : X.Adj i j
      · simp only [hij, ha, ite_false, ite_true]
        ring
      · simp only [hij, ha, ite_false]
        ring
  rw [Matrix.mulVec, dotProduct, Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _), Matrix.mulVec, dotProduct]

theorem quad_levelMat_of_eigen {α β μ : ℝ} {x : V → ℝ} (hx : X.adjMatrix ℝ *ᵥ x = μ • x)
    (hs : ∑ j, x j = 0) :
    x ⬝ᵥ (levelMat X α β *ᵥ x) = (1 - β + (α - β) * μ) * (x ⬝ᵥ x) := by
  have h : levelMat X α β *ᵥ x = (1 - β + (α - β) * μ) • x := by
    ext i
    rw [levelMat_mulVec_apply, hx, hs, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  rw [h, dotProduct_smul, smul_eq_mul]

theorem neg_nine_le_of_posSemidef {k : ℕ} (hreg : X.IsRegularOfDegree k)
    (hP : (levelMat X (1 / 8) (1 / 64)).PosSemidef) (μ : ℝ)
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ) : -9 ≤ μ := by
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hAx : X.adjMatrix ℝ *ᵥ x = μ • x := by
    have h := hx.apply_eq_smul
    rwa [Matrix.toLin'_apply] at h
  by_cases hk : μ = k
  · rw [hk]
    have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  · have hs := sum_eq_zero_of_eigen X hreg hAx hk
    have hq := hP.dotProduct_mulVec_nonneg x
    rw [star_trivial, quad_levelMat_of_eigen X hAx hs] at hq
    have hxx := dotProduct_self_pos (V := V) hx.2
    by_contra hlt
    rw [not_le] at hlt
    have hneg : (1 - 1 / 64 + (1 / 8 - 1 / 64) * μ) * (x ⬝ᵥ x) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hxx
    linarith

theorem card_le_of_posSemidef (hreg : X.IsRegularOfDegree 693)
    (hP : (levelMat X (1 / 528) (-1 / 4096)).PosSemidef) : Fintype.card V ≤ 10166 := by
  have hq := hP.dotProduct_mulVec_nonneg fun _ => 1
  rw [star_trivial] at hq
  have hA : ∀ i, (X.adjMatrix ℝ *ᵥ fun _ => (1 : ℝ)) i = 693 := fun i => by
    have h := X.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) hreg (a := 1) (v := i)
    rw [mul_one] at h
    exact h
  have hsum : ∑ _j : V, (1 : ℝ) = Fintype.card V := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hM : ∀ i, (levelMat X (1 / 528) (-1 / 4096) *ᵥ fun _ => (1 : ℝ)) i =
      (1 + 1 / 4096) + (1 / 528 + 1 / 4096) * 693 - 1 / 4096 * Fintype.card V := by
    intro i
    rw [levelMat_mulVec_apply, hA, hsum]
    ring
  have hq' : (0 : ℝ) ≤ Fintype.card V *
      ((1 + 1 / 4096) + (1 / 528 + 1 / 4096) * 693 - 1 / 4096 * Fintype.card V) := by
    have e : (fun _ => (1 : ℝ)) ⬝ᵥ (levelMat X (1 / 528) (-1 / 4096) *ᵥ fun _ => (1 : ℝ)) =
        Fintype.card V *
          ((1 + 1 / 4096) + (1 / 528 + 1 / 4096) * 693 - 1 / 4096 * Fintype.card V) := by
      simp only [dotProduct, hM, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [e] at hq
    exact hq
  by_contra hlt
  rw [not_le] at hlt
  have hn : (10166 : ℝ) < Fintype.card V := by exact_mod_cast hlt
  nlinarith

end Level

theorem reachable_of_three {V : Type*} [Fintype V] (X : SimpleGraph V)
    (hcomp : ∀ x : V, {y | X.Reachable x y}.ncard = 3510) (hcard : Fintype.card V ≤ 10166)
    (x y z : V) : X.Reachable x y ∨ X.Reachable x z ∨ X.Reachable y z := by
  by_contra h
  simp only [not_or] at h
  obtain ⟨hxy, hxz, hyz⟩ := h
  have hd1 : Disjoint {a | X.Reachable x a} {a | X.Reachable y a} :=
    Set.disjoint_left.2 fun a hx hy => hxy (hx.trans hy.symm)
  have hd2 : Disjoint ({a | X.Reachable x a} ∪ {a | X.Reachable y a}) {a | X.Reachable z a} := by
    rw [Set.disjoint_union_left]
    exact ⟨Set.disjoint_left.2 fun a hx hz => hxz (hx.trans hz.symm),
      Set.disjoint_left.2 fun a hy hz => hyz (hy.trans hz.symm)⟩
  have h3 : ({a | X.Reachable x a} ∪ {a | X.Reachable y a} ∪ {a | X.Reachable z a}).ncard =
      3510 + 3510 + 3510 := by
    rw [Set.ncard_union_eq hd2, Set.ncard_union_eq hd1, hcomp, hcomp, hcomp]
  have hle := Set.ncard_le_ncard (Set.subset_univ
    ({a | X.Reachable x a} ∪ {a | X.Reachable y a} ∪ {a | X.Reachable z a}))
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, h3] at hle
  omega

theorem connected_of_conj {V : Type*} (X : SimpleGraph V) [Nonempty V]
    (h3 : ∀ x y z : V, X.Reachable x y ∨ X.Reachable x z ∨ X.Reachable y z)
    (hconj : ∀ x y : V, ¬X.Reachable x y → ∃ a b : X →g X,
      a x = x ∧ b y = y ∧ (∀ p, b (b p) = p) ∧ a (b (a x)) = y) :
    X.Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun x y => ?_, inferInstance⟩
  by_contra hxy
  obtain ⟨a, b, hax, hby, hbb, hy⟩ := hconj x y hxy
  have hb : ∀ p, X.Reachable x p → X.Reachable x (b p) := by
    intro p hp
    rcases h3 x y (b p) with h | h | h
    · exact absurd h hxy
    · exact h
    · have h' := h.map b
      rw [hby, hbb] at h'
      exact absurd (hp.trans h'.symm) hxy
  have ha : ∀ p, X.Reachable x p → X.Reachable x (a p) := by
    intro p hp
    have h' := hp.map a
    rwa [hax] at h'
  apply hxy
  rw [← hy]
  exact ha _ (hb _ (ha _ (SimpleGraph.Reachable.refl x)))

section Iso

variable {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}

theorem card_neighborSet_iso (e : G ≃g G') (w : W) [Fintype (G'.neighborSet w)]
    [Fintype (G.neighborSet (e.symm w))] :
    Fintype.card (G'.neighborSet w) = Fintype.card (G.neighborSet (e.symm w)) :=
  Fintype.card_congr (Equiv.subtypeEquiv e.symm.toEquiv fun x => by
    rw [SimpleGraph.mem_neighborSet, SimpleGraph.mem_neighborSet]
    exact e.symm.map_adj_iff.symm)

theorem card_commonNeighbors_iso (e : G ≃g G') (w w' : W)
    [Fintype (G'.commonNeighbors w w')] [Fintype (G.commonNeighbors (e.symm w) (e.symm w'))] :
    Fintype.card (G'.commonNeighbors w w') =
      Fintype.card (G.commonNeighbors (e.symm w) (e.symm w')) :=
  Fintype.card_congr (Equiv.subtypeEquiv e.symm.toEquiv fun x => by
    rw [SimpleGraph.mem_commonNeighbors, SimpleGraph.mem_commonNeighbors]
    exact and_congr e.symm.map_adj_iff.symm e.symm.map_adj_iff.symm)

theorem isSRGWith_of_iso [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (e : G ≃g G')
    {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ) : G'.IsSRGWith n k ℓ μ where
  card := by
    rw [← h.card]
    exact (Fintype.card_congr e.toEquiv).symm
  regular w := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, card_neighborSet_iso e w,
      SimpleGraph.card_neighborSet_eq_degree]
    exact h.regular (e.symm w)
  of_adj w w' hw := by
    rw [card_commonNeighbors_iso e w w']
    exact h.of_adj _ _ (e.symm.map_adj_iff.2 hw)
  of_not_adj w w' hne hna := by
    rw [card_commonNeighbors_iso e w w']
    exact h.of_not_adj (fun h' => hne (e.symm.injective h')) fun h' => hna (e.symm.map_adj_iff.1 h')

end Iso

end CFSG.Monster.B.Generic

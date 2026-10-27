module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Monster.B.Generic

open Finset Matrix

variable {V : Type*} [Fintype V] {X : SimpleGraph V} [DecidableRel X.Adj]

private theorem posSemidef_adjMatrix_add_nine [DecidableEq V]
    (heig : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ → -9 ≤ μ) :
    (X.adjMatrix ℝ + (9 : ℝ) • (1 : Matrix V V ℝ)).PosSemidef := by
  have hB : (X.adjMatrix ℝ + (9 : ℝ) • (1 : Matrix V V ℝ)).IsHermitian :=
    (X.isHermitian_adjMatrix ℝ).add (isHermitian_one.smul (by simp))
  rw [hB.posSemidef_iff_eigenvalues_nonneg]
  intro j
  have he := hB.mulVec_eigenvectorBasis j
  have hne : (⇑(hB.eigenvectorBasis j) : V → ℝ) ≠ 0 := by
    intro h
    apply (hB.eigenvectorBasis).orthonormal.ne_zero j
    ext i
    simpa using congrFun h i
  have hev : Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ))
      (hB.eigenvalues j - 9) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⇑(hB.eigenvectorBasis j)) ?_
    refine ⟨?_, hne⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at he
    rw [sub_smul, ← he]
    abel
  have := heig _ hev
  simp only [Pi.zero_apply]
  linarith

private theorem mulVec_eq_neg_nine_of_quad [DecidableEq V]
    (heig : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ → -9 ≤ μ)
    (z : V → ℝ) (hz : z ⬝ᵥ (X.adjMatrix ℝ *ᵥ z) = -9 * (z ⬝ᵥ z)) :
    X.adjMatrix ℝ *ᵥ z = (-9 : ℝ) • z := by
  have hpsd := posSemidef_adjMatrix_add_nine heig
  have h0 : star z ⬝ᵥ (X.adjMatrix ℝ + (9 : ℝ) • (1 : Matrix V V ℝ)) *ᵥ z = 0 := by
    rw [star_trivial, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul, hz, smul_eq_mul]
    ring
  have h1 := hpsd.dotProduct_mulVec_zero_iff.mp h0
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
  rw [neg_smul, eq_neg_iff_add_eq_zero]
  exact h1

private theorem card_subtype_set_eq {s : Set V} [DecidablePred (· ∈ s)] (t : Set s) [Fintype t]
    (p : V → Prop) [DecidablePred p] (ht : ∀ u : s, u ∈ t ↔ p u) :
    Fintype.card t = #{u | u ∈ s ∧ p u} := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, (ht x.1).1 x.2⟩
      invFun := fun u => ⟨⟨u.1, u.2.1⟩, (ht _).2 u.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun u => rfl }

private theorem card_set_eq (t : Set V) [Fintype t] (p : V → Prop) [DecidablePred p]
    (ht : ∀ u, u ∈ t ↔ p u) : Fintype.card t = #{u | p u} := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquivRight ht)

private theorem degree_eq (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    (v : V) : X.degree v = 693 := by
  rw [← X.card_neighborSet_eq_degree]
  convert (hloc v).card

private theorem card_adj_adj (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    {v y : V} (hy : X.Adj v y) : #{u | X.Adj v u ∧ X.Adj y u} = 180 := by
  have h := (hloc v).regular ⟨y, hy⟩
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    card_subtype_set_eq (s := X.neighborSet v)
      ((X.induce (X.neighborSet v)).neighborSet ⟨y, hy⟩) (X.Adj y) (fun u => Iff.rfl)] at h
  rw [← h]
  congr 1

private theorem card_three (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    {v y y' : V} (hy : X.Adj v y) (hy' : X.Adj v y') (hne : y ≠ y') :
    #{u | X.Adj v u ∧ X.Adj y u ∧ X.Adj y' u} = if X.Adj y y' then 51 else 45 := by
  have key : ∀ (t : Set (X.neighborSet v)) [Fintype t],
      (∀ u : X.neighborSet v, u ∈ t ↔ X.Adj y u ∧ X.Adj y' u) →
      Fintype.card t = #{u | X.Adj v u ∧ X.Adj y u ∧ X.Adj y' u} := by
    intro t _ ht
    rw [card_subtype_set_eq (s := X.neighborSet v) t (fun u => X.Adj y u ∧ X.Adj y' u) ht]
    congr 1
  split_ifs with hadj
  · rw [← key ((X.induce (X.neighborSet v)).commonNeighbors ⟨y, hy⟩ ⟨y', hy'⟩)
      (fun u => Iff.rfl), (hloc v).of_adj ⟨y, hy⟩ ⟨y', hy'⟩ hadj]
  · have hne' : (⟨y, hy⟩ : X.neighborSet v) ≠ ⟨y', hy'⟩ := fun h => hne (congrArg Subtype.val h)
    rw [← key ((X.induce (X.neighborSet v)).commonNeighbors ⟨y, hy⟩ ⟨y', hy'⟩)
      (fun u => Iff.rfl), (hloc v).of_not_adj hne' hadj]

private theorem adj_mulVec_apply (f : V → ℝ) (y : V) :
    (X.adjMatrix ℝ *ᵥ f) y = ∑ u, if X.Adj y u then f u else 0 := by
  rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]

private theorem local_sq [DecidableEq V]
    (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    {v y : V} (hy : X.Adj v y) (f : V → ℝ) (hf : ∀ u, ¬X.Adj v u → f u = 0) :
    (X.adjMatrix ℝ *ᵥ fun u => if X.Adj v u then (X.adjMatrix ℝ *ᵥ f) u else 0) y =
      135 * f y + 6 * (X.adjMatrix ℝ *ᵥ f) y + 45 * ∑ u, f u := by
  have key : ∀ u', (∑ u, if X.Adj y u ∧ X.Adj v u ∧ X.Adj u u' then f u' else 0) =
      (45 + 135 * (if y = u' then 1 else 0) + 6 * (if X.Adj y u' then 1 else 0)) * f u' := by
    intro u'
    by_cases hu' : X.Adj v u'
    · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      congr 1
      have hc : #{u | X.Adj y u ∧ X.Adj v u ∧ X.Adj u u'} =
          #{u | X.Adj v u ∧ X.Adj y u ∧ X.Adj u' u} := by
        congr 1
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, X.adj_comm u u']
        tauto
      rw [hc]
      by_cases hyu : y = u'
      · subst hyu
        have h180 : #{u | X.Adj v u ∧ X.Adj y u ∧ X.Adj y u} = 180 := by
          simpa using card_adj_adj hloc hy
        rw [h180]
        simp
        norm_num
      · rw [card_three hloc hy hu' hyu]
        split_ifs <;> norm_num
    · simp [hf u' hu']
  calc (X.adjMatrix ℝ *ᵥ fun u => if X.Adj v u then (X.adjMatrix ℝ *ᵥ f) u else 0) y
      = ∑ u, ∑ u', if X.Adj y u ∧ X.Adj v u ∧ X.Adj u u' then f u' else 0 := by
        rw [adj_mulVec_apply]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [adj_mulVec_apply]
        by_cases h1 : X.Adj y u <;> by_cases h2 : X.Adj v u <;> simp [h1, h2]
    _ = ∑ u', ∑ u, if X.Adj y u ∧ X.Adj v u ∧ X.Adj u u' then f u' else 0 := Finset.sum_comm
    _ = ∑ u', (45 + 135 * (if y = u' then 1 else 0) + 6 * (if X.Adj y u' then 1 else 0)) *
          f u' := Finset.sum_congr rfl fun u' _ => key u'
    _ = 135 * f y + 6 * (X.adjMatrix ℝ *ᵥ f) y + 45 * ∑ u, f u := by
        rw [adj_mulVec_apply]
        simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        ring

private theorem eigvec_of_local [DecidableEq V]
    (heig : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ → -9 ≤ μ)
    {v : V} (z : V → ℝ) (hz : ∀ u, ¬X.Adj v u → z u = 0)
    (hU : ∀ y, X.Adj v y → (X.adjMatrix ℝ *ᵥ z) y = -9 * z y) :
    X.adjMatrix ℝ *ᵥ z = (-9 : ℝ) • z := by
  apply mulVec_eq_neg_nine_of_quad heig
  simp only [dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : X.Adj v y
  · rw [hU y hy]; ring
  · rw [hz y hy]; ring

variable (X) in
private def ind2 (v w : V) : V → ℝ := fun u => if X.Adj v u ∧ X.Adj w u then 1 else 0

variable (X) in
private def ind1 (v : V) : V → ℝ := fun u => if X.Adj v u then 1 else 0

variable (X) in
private def restr (v : V) (g : V → ℝ) : V → ℝ := fun u => if X.Adj v u then g u else 0

variable (X) in
private noncomputable def defect (v w : V) : V → ℝ :=
  restr X v (X.adjMatrix ℝ *ᵥ ind2 X v w) - (15 : ℝ) • ind2 X v w -
    (5 * (#{u | X.Adj v u ∧ X.Adj w u} : ℝ) / 21) • ind1 X v

private theorem defect_supp {v w u : V} (hu : ¬X.Adj v u) : defect X v w u = 0 := by
  simp [defect, restr, ind2, ind1, hu]

private theorem mulVec_ind1 (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    {v y : V} (hy : X.Adj v y) : (X.adjMatrix ℝ *ᵥ ind1 X v) y = 180 := by
  rw [adj_mulVec_apply]
  have : (∑ u, if X.Adj y u then ind1 X v u else 0) =
      ∑ u, if X.Adj v u ∧ X.Adj y u then 1 else 0 := by
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h1 : X.Adj y u <;> by_cases h2 : X.Adj v u <;> simp [ind1, h1, h2]
  rw [this, Finset.sum_boole, card_adj_adj hloc hy]
  norm_num

private theorem sum_ind2 (v w : V) :
    ∑ u, ind2 X v w u = (#{u | X.Adj v u ∧ X.Adj w u} : ℝ) := by
  simp [ind2, Finset.sum_boole]

private theorem mulVec_defect_local [DecidableEq V]
    (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    {v w y : V} (hy : X.Adj v y) :
    (X.adjMatrix ℝ *ᵥ defect X v w) y = -9 * defect X v w y := by
  have h1 := local_sq hloc hy (ind2 X v w) (fun u hu => by simp [ind2, hu])
  have h2 : (fun u => if X.Adj v u then (X.adjMatrix ℝ *ᵥ ind2 X v w) u else 0) =
      restr X v (X.adjMatrix ℝ *ᵥ ind2 X v w) := rfl
  rw [h2, sum_ind2] at h1
  rw [defect, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, mulVec_ind1 hloc hy]
  simp only [restr, ind1, hy, ite_true]
  ring

private theorem mulVec_defect [DecidableEq V]
    (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    (heig : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ → -9 ≤ μ)
    (v w : V) : X.adjMatrix ℝ *ᵥ defect X v w = (-9 : ℝ) • defect X v w :=
  eigvec_of_local heig _ (fun _ hu => defect_supp hu) (fun _ hy => mulVec_defect_local hloc hy)

private theorem dotProduct_restr {v : V} {h : V → ℝ} (hh : ∀ u, ¬X.Adj v u → h u = 0)
    (g : V → ℝ) : h ⬝ᵥ restr X v g = h ⬝ᵥ g := by
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : X.Adj v u
  · simp [restr, hu]
  · simp [hh u hu]

private theorem dotProduct_ind2 {v : V} {h : V → ℝ} (hh : ∀ u, ¬X.Adj v u → h u = 0) (w : V) :
    h ⬝ᵥ ind2 X v w = (X.adjMatrix ℝ *ᵥ h) w := by
  rw [adj_mulVec_apply]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : X.Adj v u
  · by_cases hwu : X.Adj w u <;> simp [ind2, hu, hwu]
  · simp [hh u hu]

private theorem dotProduct_ind1 (v : V) (h : V → ℝ) :
    h ⬝ᵥ ind1 X v = (X.adjMatrix ℝ *ᵥ h) v := by
  rw [adj_mulVec_apply]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : X.Adj v u <;> simp [ind1, hu]

private theorem dotProduct_mulVec_adj (h f : V → ℝ) :
    h ⬝ᵥ (X.adjMatrix ℝ *ᵥ f) = (X.adjMatrix ℝ *ᵥ h) ⬝ᵥ f := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, SimpleGraph.transpose_adjMatrix]

private theorem defect_eq_zero [DecidableEq V]
    (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    (heig : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ → -9 ≤ μ)
    {v w : V} (hvw : ¬X.Adj v w) : defect X v w = 0 := by
  have hA := mulVec_defect hloc heig v w
  have hs : ∀ u, ¬X.Adj v u → defect X v w u = 0 := fun _ hu => defect_supp hu
  have e3 : defect X v w ⬝ᵥ ind2 X v w = 0 := by
    rw [dotProduct_ind2 hs, hA]
    simp [defect_supp hvw]
  have e4 : defect X v w ⬝ᵥ ind1 X v = 0 := by
    rw [dotProduct_ind1, hA]
    simp [defect_supp (fun h : X.Adj v v => X.irrefl h)]
  have e1 : defect X v w ⬝ᵥ restr X v (X.adjMatrix ℝ *ᵥ ind2 X v w) = 0 := by
    rw [dotProduct_restr hs, dotProduct_mulVec_adj, hA, smul_dotProduct, e3, smul_zero]
  apply dotProduct_self_eq_zero.mp
  conv_lhs => arg 2; rw [defect]
  rw [dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul, e1, e3, e4]
  simp

private theorem local_indicator [DecidableEq V]
    (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    (heig : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ → -9 ≤ μ)
    {v w : V} (hvw : ¬X.Adj v w) {y : V} (hy : X.Adj v y) :
    (#{u | X.Adj y u ∧ X.Adj v u ∧ X.Adj w u} : ℝ) =
      15 * (if X.Adj w y then 1 else 0) + 5 * (#{u | X.Adj v u ∧ X.Adj w u} : ℝ) / 21 := by
  have h0 := congrFun (defect_eq_zero hloc heig hvw) y
  simp only [defect, restr, ind1, hy, ite_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply] at h0
  have hfy : ind2 X v w y = if X.Adj w y then 1 else 0 := by simp [ind2, hy]
  have hAf : (X.adjMatrix ℝ *ᵥ ind2 X v w) y =
      (#{u | X.Adj y u ∧ X.Adj v u ∧ X.Adj w u} : ℝ) := by
    rw [adj_mulVec_apply, ← Finset.sum_boole]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h1 : X.Adj y u <;> simp [ind2, h1]
  rw [← hfy, ← hAf]
  linarith

private theorem card_common_eq [DecidableEq V]
    (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    (heig : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ → -9 ≤ μ)
    {v w x : V} (hne : v ≠ w) (hvw : ¬X.Adj v w) (hx1 : X.Adj v x) (hx2 : X.Adj w x) :
    #{u | X.Adj v u ∧ X.Adj w u} = 126 := by
  have h1 := local_indicator hloc heig hvw hx1
  have h3 := card_three hloc hx1.symm hx2.symm hne
  rw [ite_eq_right hvw] at h3
  rw [ite_eq_left hx2, h3] at h1
  have : (#{u | X.Adj v u ∧ X.Adj w u} : ℝ) = 126 := by linarith
  exact_mod_cast this

private theorem exists_adj_of_dist_two [DecidableEq V]
    (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    (heig : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ → -9 ≤ μ)
    {v w : V} (hne : v ≠ w) (hvw : ¬X.Adj v w) (hx : ∃ x, X.Adj v x ∧ X.Adj w x) {y : V}
    (hwy : X.Adj w y) (hvy : ¬X.Adj v y) : ∃ u, X.Adj v u ∧ X.Adj y u := by
  obtain ⟨x, hx1, hx2⟩ := hx
  have h126 := card_common_eq hloc heig hne.symm (fun h => hvw h.symm) hx2 hx1
  have h1 := local_indicator hloc heig (v := w) (w := v) (fun h => hvw h.symm) hwy
  rw [ite_eq_right hvy, h126] at h1
  by_contra hcon
  have h0 : #{u | X.Adj y u ∧ X.Adj w u ∧ X.Adj v u} = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro u - ⟨hyu, -, hvu⟩
    exact hcon ⟨u, hvu, hyu⟩
  rw [h0] at h1
  norm_num at h1

private theorem near_of_adj [DecidableEq V]
    (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    (heig : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ → -9 ≤ μ)
    {v u u' : V} (hu : u = v ∨ X.Adj v u ∨ ∃ x, X.Adj v x ∧ X.Adj x u) (hadj : X.Adj u u') :
    u' = v ∨ X.Adj v u' ∨ ∃ x, X.Adj v x ∧ X.Adj x u' := by
  rcases hu with rfl | hvu | ⟨x, hvx, hxu⟩
  · exact Or.inr (Or.inl hadj)
  · exact Or.inr (Or.inr ⟨u, hvu, hadj⟩)
  · by_cases h1 : u' = v
    · exact Or.inl h1
    by_cases h2 : X.Adj v u'
    · exact Or.inr (Or.inl h2)
    by_cases h3 : u = v
    · subst h3
      exact Or.inr (Or.inl hadj)
    by_cases h4 : X.Adj v u
    · exact Or.inr (Or.inr ⟨u, h4, hadj⟩)
    obtain ⟨y, hvy, hyu'⟩ :=
      exists_adj_of_dist_two hloc heig (Ne.symm h3) h4 ⟨x, hvx, hxu.symm⟩ hadj h2
    exact Or.inr (Or.inr ⟨y, hvy, hyu'.symm⟩)

private theorem near_of_reachable [DecidableEq V]
    (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    (heig : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ → -9 ≤ μ)
    {v u : V} (h : X.Reachable v u) : u = v ∨ X.Adj v u ∨ ∃ x, X.Adj v x ∧ X.Adj x u := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hbc ih => exact near_of_adj hloc heig ih hbc

omit [Fintype V] [DecidableRel X.Adj] in
private theorem reachable_of_near {v u : V}
    (h : u = v ∨ X.Adj v u ∨ ∃ x, X.Adj v x ∧ X.Adj x u) : X.Reachable v u := by
  rcases h with rfl | h | ⟨x, h1, h2⟩
  · rfl
  · exact h.reachable
  · exact h1.reachable.trans h2.reachable

private theorem mem_supp_iff_near [DecidableEq V]
    (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    (heig : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ → -9 ≤ μ)
    (v u : V) :
    u ∈ (X.connectedComponentMk v).supp ↔ u = v ∨ X.Adj v u ∨ ∃ x, X.Adj v x ∧ X.Adj x u := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
  exact ⟨fun h => near_of_reachable hloc heig h.symm, fun h => (reachable_of_near h).symm⟩

private theorem card_filter_split (P Q R S : V → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred R] [DecidablePred S] (h : ∀ u, P u ↔ Q u ∨ R u ∨ S u)
    (h1 : ∀ u, Q u → ¬R u) (h2 : ∀ u, Q u → ¬S u) (h3 : ∀ u, R u → ¬S u) :
    #{u | P u} = #{u | Q u} + #{u | R u} + #{u | S u} := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hu := h u
  have h1u := h1 u
  have h2u := h2 u
  have h3u := h3 u
  clear h h1 h2 h3
  by_cases hq : Q u <;> by_cases hr : R u <;> by_cases hs : S u <;> simp_all

private theorem card_sphere_above [DecidableEq V]
    (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    {v y : V} (hy : X.Adj v y) : #{u | X.Adj y u ∧ u ≠ v ∧ ¬X.Adj v u} = 512 := by
  have h := card_filter_split (fun u => X.Adj y u) (fun u => X.Adj y u ∧ u = v)
    (fun u => X.Adj v u ∧ X.Adj y u) (fun u => X.Adj y u ∧ u ≠ v ∧ ¬X.Adj v u)
    (fun u => by by_cases h : u = v <;> by_cases h' : X.Adj v u <;> simp_all [eq_comm])
    (fun u hq hr => by rw [hq.2] at hr; exact X.irrefl hr.1)
    (fun u hq hs => hs.2.1 hq.2) (fun u hr hs => hs.2.2 hr.1)
  have hdeg : #{u | X.Adj y u} = 693 := by
    rw [← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree,
      degree_eq hloc]
  have hone : #{u | X.Adj y u ∧ u = v} = 1 := by
    rw [Finset.card_eq_one]
    exact ⟨v, by ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]; exact ⟨fun h => h.2, fun h => ⟨h ▸ hy.symm, h⟩⟩⟩
  rw [hdeg, hone, card_adj_adj hloc hy] at h
  omega

private theorem card_sphere [DecidableEq V]
    (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    (heig : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ → -9 ≤ μ)
    (v : V) : #{u | u ≠ v ∧ ¬X.Adj v u ∧ ∃ x, X.Adj v x ∧ X.Adj x u} = 2816 := by
  have h := Finset.card_mul_eq_card_mul X.Adj (s := X.neighborFinset v)
    (t := {u | u ≠ v ∧ ¬X.Adj v u ∧ ∃ x, X.Adj v x ∧ X.Adj x u}) (m := 512) (n := 126) ?_ ?_
  · rw [SimpleGraph.card_neighborFinset_eq_degree, degree_eq hloc] at h
    omega
  · intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    rw [← card_sphere_above hloc hy, Finset.bipartiteAbove, Finset.filter_filter]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h.2, h.1.1, h.1.2.1⟩, fun h => ⟨⟨h.2.1, h.2.2, y, hy, h.1⟩, h.1⟩⟩
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨hwv, hvw, x, hx1, hx2⟩ := hw
    rw [← card_common_eq hloc heig (Ne.symm hwv) hvw hx1 hx2.symm, Finset.bipartiteBelow,
      SimpleGraph.neighborFinset_eq_filter, Finset.filter_filter]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, X.adj_comm u w]

private theorem card_component [DecidableEq V]
    (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    (heig : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ → -9 ≤ μ)
    (v : V) : Fintype.card (X.connectedComponentMk v).supp = 3510 := by
  rw [card_set_eq _ _ (mem_supp_iff_near hloc heig v)]
  rw [card_filter_split _ (fun u => u = v) (fun u => X.Adj v u)
    (fun u => u ≠ v ∧ ¬X.Adj v u ∧ ∃ x, X.Adj v x ∧ X.Adj x u)
    (fun u => by by_cases h : u = v <;> by_cases h' : X.Adj v u <;> simp_all)
    (fun u hq hr => by rw [hq] at hr; exact X.irrefl hr)
    (fun u hq hs => hs.1 hq) (fun u hr hs => hs.2.1 hr)]
  rw [card_sphere hloc heig v, ← SimpleGraph.neighborFinset_eq_filter,
    SimpleGraph.card_neighborFinset_eq_degree, degree_eq hloc, Finset.filter_eq']
  simp

private theorem isSRGWith_component [DecidableEq V]
    (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    (heig : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ → -9 ≤ μ)
    (v : V) : (X.induce (X.connectedComponentMk v).supp).IsSRGWith 3510 693 180 126 where
  card := card_component hloc heig v
  regular a := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset, degree_eq hloc]
    intro u hu
    exact ((X.connectedComponentMk v).mem_supp_congr_adj hu).mp a.2
  of_adj a b hab := by
    rw [card_subtype_set_eq ((X.induce (X.connectedComponentMk v).supp).commonNeighbors a b)
      (fun u => X.Adj a u ∧ X.Adj b u) (fun u => Iff.rfl), ← card_adj_adj hloc hab]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2,
      fun h => ⟨((X.connectedComponentMk v).mem_supp_congr_adj h.1).mp a.2, h⟩⟩
  of_not_adj a b hne hnadj := by
    have hr : X.Reachable a b := by
      have ha := a.2
      have hb := b.2
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha hb
      exact SimpleGraph.ConnectedComponent.exact (ha.trans hb.symm)
    have hne' : (a : V) ≠ b := fun h => hne (Subtype.ext h)
    rcases near_of_reachable hloc heig hr with h | h | ⟨x, hx1, hx2⟩
    · exact absurd h.symm hne'
    · exact absurd h hnadj
    rw [card_subtype_set_eq ((X.induce (X.connectedComponentMk v).supp).commonNeighbors a b)
      (fun u => X.Adj a u ∧ X.Adj b u) (fun u => Iff.rfl),
      ← card_common_eq hloc heig hne' hnadj hx1 hx2.symm]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2,
      fun h => ⟨((X.connectedComponentMk v).mem_supp_congr_adj h.1).mp a.2, h⟩⟩

theorem locally_unitary_graph_least_eigenvalue_rigidity {V : Type*} [Fintype V]
    [DecidableEq V] (X : SimpleGraph V) [DecidableRel X.Adj]
    (hloc : ∀ v, (X.induce (X.neighborSet v)).IsSRGWith 693 180 51 45)
    (heig : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ → -9 ≤ μ) :
    (∀ c : X.ConnectedComponent, (X.induce c.supp).diam = 2 ∧
      (X.induce c.supp).IsSRGWith 3510 693 180 126) ∧
    ∀ v w, X.dist v w = 2 → Fintype.card (X.commonNeighbors v w) = 126 := by
  refine ⟨fun c => ?_, fun v w hd => ?_⟩
  · refine SimpleGraph.ConnectedComponent.ind (fun v => ?_) c
    have hsrg := isSRGWith_component hloc heig v
    refine ⟨?_, hsrg⟩
    have hnt : Nontrivial (X.connectedComponentMk v).supp := by
      rw [← Fintype.one_lt_card_iff_nontrivial, hsrg.card]
      norm_num
    have hne : X.induce (X.connectedComponentMk v).supp ≠ ⊤ := by
      intro htop
      obtain ⟨w, hw⟩ : ∃ w, w ≠ v ∧ ¬X.Adj v w ∧ ∃ x, X.Adj v x ∧ X.Adj x w := by
        have h := card_sphere hloc heig v
        obtain ⟨w, hw⟩ := Finset.card_pos.mp (by rw [h]; norm_num)
        exact ⟨w, by simpa using hw⟩
      have hv : v ∈ (X.connectedComponentMk v).supp :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      have hw' : w ∈ (X.connectedComponentMk v).supp :=
        (mem_supp_iff_near hloc heig v w).mpr (Or.inr (Or.inr hw.2.2))
      have hadj : (X.induce (X.connectedComponentMk v).supp).Adj ⟨v, hv⟩ ⟨w, hw'⟩ := by
        rw [htop]
        simpa using Ne.symm hw.1
      exact hw.2.1 hadj
    rw [SimpleGraph.diam, hsrg.ediam_eq_two hne (by norm_num)]
    rfl
  · have hed : X.edist v w = 2 := by
      rw [SimpleGraph.dist] at hd
      exact_mod_cast (ENat.toNat_eq_iff (by norm_num)).mp hd
    obtain ⟨hne, hnadj, x, hx⟩ := SimpleGraph.edist_eq_two_iff.mp hed
    rw [SimpleGraph.mem_commonNeighbors] at hx
    rw [card_set_eq (X.commonNeighbors v w) (fun u => X.Adj v u ∧ X.Adj w u) (fun u => Iff.rfl)]
    exact card_common_eq hloc heig hne hnadj hx.1 hx.2

end CFSG.Monster.B.Generic

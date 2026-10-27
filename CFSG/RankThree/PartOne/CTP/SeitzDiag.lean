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
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.RankThree.PartOne.CTP

open scoped MatrixGroups Polynomial

namespace SeitzDiag

theorem mem_iSup_eigenspace_of_prod_apply_eq_zero {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (f : Module.End K V) (s : Finset K) (v : V)
    (hv : Polynomial.aeval f (∏ a ∈ s, (Polynomial.X - Polynomial.C a)) v = 0) :
    v ∈ ⨆ a ∈ s, f.eigenspace a := by
  classical
  induction s using Finset.induction_on generalizing v with
  | empty => simp at hv; simp [hv]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, map_mul, Module.End.mul_apply] at hv
    set A : Module.End K V := Polynomial.aeval f (Polynomial.X - Polynomial.C a) with hA
    set g : Module.End K V := Polynomial.aeval f (∏ b ∈ s, (Polynomial.X - Polynomial.C b))
    have hAg : Commute A g := (Commute.all _ _).map (Polynomial.aeval f)
    have hAv : A v ∈ ⨆ b ∈ s, f.eigenspace b := by
      apply ih
      change (g * A) v = 0
      rw [← hAg.eq, Module.End.mul_apply]
      exact hv
    have hU : (⨆ b ∈ s, f.eigenspace b) ≤ (⨆ b ∈ s, f.eigenspace b).map A := by
      refine iSup₂_le fun b hb u hu => ?_
      have hba : b - a ≠ 0 := sub_ne_zero.mpr fun h => ha (h ▸ hb)
      have hmem : (b - a)⁻¹ • u ∈ ⨆ b ∈ s, f.eigenspace b :=
        Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem hb hu))
      refine ⟨_, hmem, ?_⟩
      have hfu : f u = b • u := Module.End.mem_eigenspace_iff.mp hu
      simp [hA, hfu, smul_smul, ← sub_smul, hba]
    obtain ⟨y, hy, hyv⟩ := hU hAv
    have hva : v - y ∈ f.eigenspace a := by
      rw [Module.End.mem_eigenspace_iff]
      have : A (v - y) = 0 := by rw [map_sub, hyv, sub_self]
      simpa [hA, sub_eq_zero] using this
    have h1 : v - y ∈ ⨆ b ∈ insert a s, f.eigenspace b :=
      Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem (Finset.mem_insert_self a s) hva)
    have h2 : (⨆ b ∈ s, f.eigenspace b) ≤ ⨆ b ∈ insert a s, f.eigenspace b :=
      biSup_mono fun b hb => Finset.mem_insert_of_mem hb
    simpa using Submodule.add_mem _ h1 (h2 hy)

theorem iSup_eigenspace_eq_top_of_pow_eq_one {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] {p : ℕ} (hp : 0 < p) {ζ : F} (hζ : IsPrimitiveRoot ζ p) (T : Module.End F V)
    (hT : T ^ p = 1) : ⨆ μ, T.eigenspace μ = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  have h0 : Polynomial.aeval T (∏ a ∈ Polynomial.nthRootsFinset p (1 : F),
      (Polynomial.X - Polynomial.C a)) = 0 := by
    rw [← Polynomial.X_pow_sub_one_eq_prod hp hζ]
    simp [hT]
  have h1 := mem_iSup_eigenspace_of_prod_apply_eq_zero T _ v (by rw [h0]; rfl)
  have h2 : (⨆ a ∈ Polynomial.nthRootsFinset p (1 : F), T.eigenspace a) ≤ ⨆ μ, T.eigenspace μ :=
    iSup₂_le_iSup _ _
  exact h2 h1

theorem span_commonEigenvectors_eq_top {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : ι → Module.End F V) (hcomm : ∀ i j, Commute (T i) (T j))
    (hss : ∀ i, (T i).IsSemisimple) (hdiag : ∀ i, ⨆ μ, (T i).eigenspace μ = ⊤) :
    Submodule.span F {v : V | ∀ i, ∃ μ : F, T i v = μ • v} = ⊤ := by
  have h1 : ∀ i, ⨆ μ, (T i).maxGenEigenspace μ = ⊤ := fun i => by
    simpa only [(hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using hdiag i
  have h2 :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      T (fun i j _ => hcomm i j) h1
  refine eq_top_iff.mpr ?_
  rw [← h2]
  refine iSup_le fun χ m hm => Submodule.subset_span fun i => ⟨χ i, ?_⟩
  have := (Submodule.mem_iInf _).mp hm i
  rwa [(hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
    Module.End.mem_eigenspace_iff] at this

theorem exists_basis_subset_of_span_eq_top {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {n : ℕ} (hn : Module.finrank F V = n) (S : Set V)
    (hS : Submodule.span F S = ⊤) : ∃ b : Module.Basis (Fin n) F V, ∀ i, b i ∈ S := by
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent F S
  let b : Module.Basis t F V := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hS])
  have hb : ∀ i, b i = (i : V) := fun i => by simp [b]
  have : Finite t := Module.Finite.finite_basis b
  have hcard : Nat.card t = n := by rw [← hn, Module.finrank_eq_nat_card_basis b]
  refine ⟨b.reindex (Finite.equivFinOfCardEq hcard), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hb]
  exact hts (Subtype.coe_prop _)

theorem squarefree_X_pow_sub_one {F : Type*} [Field F] {p : ℕ} [NeZero p] {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) : Squarefree (Polynomial.X ^ p - 1 : F[X]) := by
  have : NeZero (p : F) := hζ.neZero'
  simpa using (Polynomial.separable_X_pow_sub_C (n := p) (1 : F) NeZero.out one_ne_zero).squarefree

end SeitzDiag

theorem exists_conj_diagonal_of_exponent_prime {F : Type*} [Field F] {n p : ℕ} [Fact p.Prime]
    (hζ : ∃ ζ : F, IsPrimitiveRoot ζ p) (E : Subgroup (GL (Fin n) F))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1) :
    ∃ g : GL (Fin n) F, ∀ x ∈ E, ∀ i j : Fin n, i ≠ j →
      ((g * x * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0 := by
  obtain ⟨ζ, hζ⟩ := hζ
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have : NeZero p := ⟨hp.ne'⟩
  let T : E → Module.End F (Fin n → F) := fun x =>
    Matrix.toLinAlgEquiv' ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hTcomm : ∀ x y, Commute (T x) (T y) := fun x y => by
    have h := congrArg Units.val (hcomm x x.2 y y.2)
    simp only [Units.val_mul] at h
    change Matrix.toLinAlgEquiv' _ * Matrix.toLinAlgEquiv' _ =
      Matrix.toLinAlgEquiv' _ * Matrix.toLinAlgEquiv' _
    rw [← map_mul, ← map_mul, h]
  have hTpow : ∀ x, T x ^ p = 1 := fun x => by
    change Matrix.toLinAlgEquiv' _ ^ p = 1
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hexp x x.2, Units.val_one, map_one]
  have hss : ∀ x, (T x).IsSemisimple := fun x =>
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero (SeitzDiag.squarefree_X_pow_sub_one hζ)
      (by simp [hTpow x])
  have hdiag : ∀ x, ⨆ μ, (T x).eigenspace μ = ⊤ := fun x =>
    SeitzDiag.iSup_eigenspace_eq_top_of_pow_eq_one hp hζ (T x) (hTpow x)
  have hspan := SeitzDiag.span_commonEigenvectors_eq_top T hTcomm hss hdiag
  obtain ⟨B, hB⟩ :=
    SeitzDiag.exists_basis_subset_of_span_eq_top (Module.finrank_fin_fun F) _ hspan
  let e := Pi.basisFun F (Fin n)
  obtain ⟨g, hg, hginv⟩ : ∃ g : GL (Fin n) F, (g : Matrix (Fin n) (Fin n) F) = B.toMatrix e ∧
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = e.toMatrix B :=
    ⟨⟨B.toMatrix e, e.toMatrix B, B.toMatrix_mul_toMatrix_flip e,
      e.toMatrix_mul_toMatrix_flip B⟩, rfl, rfl⟩
  refine ⟨g, fun x hx i j hij => ?_⟩
  have h1 : ((g * x * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      LinearMap.toMatrix B B (T ⟨x, hx⟩) := by
    have h2 : LinearMap.toMatrix e e (T ⟨x, hx⟩) = (x : Matrix (Fin n) (Fin n) F) :=
      LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' _
    rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix B e B e (T ⟨x, hx⟩), h2,
      Units.val_mul, Units.val_mul, hg, hginv]
  rw [h1, LinearMap.toMatrix_apply]
  obtain ⟨μ, hμ⟩ := hB j ⟨x, hx⟩
  rw [hμ, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_of_ne hij, smul_zero]

end CFSG.RankThree.PartOne.CTP

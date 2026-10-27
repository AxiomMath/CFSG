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

open Module Module.End Polynomial

namespace CFSG.RankThree.PartOne

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem ker_aeval_prod_X_sub_C_eq_iSup (f : End K V) (s : Finset K) :
    LinearMap.ker (aeval f (∏ a ∈ s, (X - C a) : K[X])) = ⨆ a ∈ s, f.eigenspace a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, map_one, Finset.notMem_empty, iSup_false, iSup_bot]
    rw [Module.End.one_eq_id]; exact LinearMap.ker_id
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.iSup_insert, ← ih]
    have hcop : IsCoprime (X - C a : K[X]) (∏ b ∈ s, (X - C b)) :=
      IsCoprime.prod_right fun b hb =>
        Polynomial.isCoprime_X_sub_C_of_isUnit_sub
          (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr fun h => ha (h ▸ hb)))
    rw [← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop]
    congr 1
    ext v
    simp only [LinearMap.mem_ker, map_sub, aeval_X, aeval_C, LinearMap.sub_apply,
      Module.End.mem_eigenspace_iff, algebraMap_end_apply, sub_eq_zero]

theorem iSup_eigenspace_eq_top_of_pow_eq_one {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {f : End K V} (hf : f ^ p = 1) : ⨆ μ, f.eigenspace μ = ⊤ := by
  have h1 : aeval f (X ^ p - 1 : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, map_one, hf, sub_self]
  rw [Polynomial.X_pow_sub_one_eq_prod (Nat.pos_of_ne_zero (NeZero.ne p)) hζ] at h1
  have h2 := ker_aeval_prod_X_sub_C_eq_iSup f (Polynomial.nthRootsFinset p (1 : K))
  rw [h1, LinearMap.ker_zero] at h2
  refine top_unique ?_
  rw [h2]
  exact iSup₂_le fun a _ => le_iSup (fun μ => f.eigenspace μ) a


theorem isSemisimple_of_pow_eq_one {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {f : End K V} (hf : f ^ p = 1) : f.IsSemisimple := by
  have : NeZero (p : K) := hζ.neZero'
  refine isSemisimple_of_squarefree_aeval_eq_zero (p := (X ^ p - 1 : K[X])) ?_ ?_
  · simpa using (separable_X_pow_sub_C (1 : K) (NeZero.ne (p : K)) one_ne_zero).squarefree
  · rw [map_sub, map_pow, aeval_X, map_one, hf, sub_self]

theorem exists_basis_common_eigenvectors_of_pow_eq_one {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) [FiniteDimensional K V] {ι : Type*} [Finite ι]
    (f : ι → End K V) (hcomm : ∀ i j, Commute (f i) (f j)) (hpow : ∀ i, f i ^ p = 1) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (μ : ι → Fin (finrank K V) → K),
      ∀ i j, f i (b j) = μ i j • b j := by
  classical
  have hss := fun i => isSemisimple_of_pow_eq_one hζ (hpow i)
  have hspan : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤ := fun i =>
    ((hss i).iSup_maxGenEigenspace_eq_top_iff).2 (iSup_eigenspace_eq_top_of_pow_eq_one hζ (hpow i))
  set W : (ι → K) → Submodule K V := fun χ => ⨅ i, (f i).maxGenEigenspace (χ i) with hWdef
  have hW : ∀ (χ : ι → K) (i : ι), (f i).maxGenEigenspace (χ i) = (f i).eigenspace (χ i) :=
    fun χ i => (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace _
  have htop : ⨆ χ, W χ = ⊤ :=
    iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      (fun i j _ => hcomm i j) hspan
  have hind : iSupIndep W :=
    independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      fun i j φ => mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let bW := fun χ => Basis.ofVectorSpace K (W χ)
  let b₀ := hint.collectedBasis bW
  have : Finite (Σ χ, Basis.ofVectorSpaceIndex K (W χ)) := Module.Finite.finite_basis b₀
  let e₀ : (Σ χ, Basis.ofVectorSpaceIndex K (W χ)) ≃ Fin (finrank K V) :=
    (Finite.equivFin _).trans (finCongr (finrank_eq_nat_card_basis b₀).symm)
  refine ⟨b₀.reindex e₀, fun i j => (e₀.symm j).1 i, fun i j => ?_⟩
  have hmem : b₀ (e₀.symm j) ∈ W (e₀.symm j).1 := hint.collectedBasis_mem bW (e₀.symm j)
  rw [Basis.reindex_apply]
  have hi := (Submodule.mem_iInf _).mp hmem i
  rw [hW] at hi
  exact mem_eigenspace_iff.mp hi

theorem exists_basis_common_eigenvectors_of_pow_eq_scalar {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) [FiniteDimensional K V] {ι : Type*} [Finite ι]
    (f : ι → End K V) (r : ι → K) (hcomm : ∀ i j, Commute (f i) (f j))
    (hr : ∀ i, r i ≠ 0) (hpow : ∀ i, f i ^ p = (r i ^ p) • (1 : End K V)) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (μ : ι → Fin (finrank K V) → K),
      (∀ i j, f i (b j) = μ i j • b j) ∧
      (∀ i j, μ i j ^ p = r i ^ p) ∧
      (∀ i j, μ i j ≠ 0) := by
  classical
  let g : ι → End K V := fun i => (r i)⁻¹ • f i
  have hgpow : ∀ i, g i ^ p = 1 := by
    intro i
    dsimp only [g]
    rw [_root_.smul_pow, hpow i, smul_smul, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero p (hr i)), one_smul]
  have hgcomm : ∀ i j, Commute (g i) (g j) := by
    intro i j
    exact ((hcomm i j).smul_left (r i)⁻¹).smul_right (r j)⁻¹
  obtain ⟨b, μ, hb⟩ :=
    exists_basis_common_eigenvectors_of_pow_eq_one (p := p) (ζ := ζ) hζ g hgcomm hgpow
  have hμ : ∀ i j, μ i j ^ p = 1 := by
    intro i j
    have hev : (g i).HasEigenvector (μ i j) (b j) :=
      Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (hb i j), b.ne_zero j⟩
    have hp := hev.pow_apply p
    rw [hgpow i] at hp
    have h1 : μ i j ^ p • b j = (1 : K) • b j := by
      rw [one_smul]
      simpa using hp.symm
    exact smul_left_injective K (b.ne_zero j) h1
  refine ⟨b, fun i j => r i * μ i j, ?_, ?_, ?_⟩
  · intro i j
    have hfg : r i • g i = f i := by
      dsimp only [g]
      rw [smul_smul, mul_inv_cancel₀ (hr i), one_smul]
    calc
      f i (b j) = (r i • g i) (b j) := by rw [hfg]
      _ = r i • g i (b j) := rfl
      _ = r i • (μ i j • b j) := by rw [hb i j]
      _ = (r i * μ i j) • b j := smul_smul ..
  · intro i j
    rw [mul_pow, hμ i j, mul_one]
  · intro i j
    exact mul_ne_zero (hr i) (by
      intro h0
      have hμij := hμ i j
      rw [h0, zero_pow (NeZero.ne p)] at hμij
      exact zero_ne_one hμij)

open Matrix in
theorem exists_conj_diagonal_of_commuting_pow_eq_one {n p : ℕ} [NeZero p] {k : Type*} [Field k]
    [Finite k] {ζ : k} (hζ : IsPrimitiveRoot ζ p)
    (E₀ : Subgroup (SpecialLinearGroup (Fin n) k))
    (hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) (hpow : ∀ x ∈ E₀, x ^ p = 1) :
    ∃ A : GL (Fin n) k, ∀ x ∈ E₀, ∀ i j, i ≠ j →
      ((A : Matrix (Fin n) (Fin n) k) * (x : Matrix (Fin n) (Fin n) k) *
        ((A⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) i j = 0 := by
  classical
  have : Finite E₀ := Subtype.finite
  let f : E₀ → End k (Fin n → k) := fun x => Matrix.toLinAlgEquiv' (x : Matrix (Fin n) (Fin n) k)
  have hf_comm : ∀ x y, Commute (f x) (f y) := fun x y => by
    have h2 : ((x : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) *
        ((y : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        ((y : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) *
          ((x : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      simpa using congrArg (fun g : SpecialLinearGroup (Fin n) k => (g : Matrix (Fin n) (Fin n) k))
        (hcomm x x.2 y y.2)
    show f x * f y = f y * f x
    simp only [f, ← map_mul, h2]
  have hf_pow : ∀ x, f x ^ p = 1 := fun x => by
    have h2 : ((x : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) ^ p = 1 := by
      simpa using congrArg (fun g : SpecialLinearGroup (Fin n) k => (g : Matrix (Fin n) (Fin n) k))
        (hpow x x.2)
    simp only [f, ← map_pow, h2, map_one]
  obtain ⟨b, μ, hb⟩ := exists_basis_common_eigenvectors_of_pow_eq_one hζ f hf_comm hf_pow
  let b' : Basis (Fin n) k (Fin n → k) := b.reindex (finCongr (Module.finrank_fin_fun k))
  have hb' : ∀ (x : E₀) (j : Fin n), f x (b' j) = μ x ((finCongr (Module.finrank_fin_fun k)).symm j)
      • b' j := fun x j => by
    simp only [b', Basis.reindex_apply]
    exact hb x _
  let P : Matrix (Fin n) (Fin n) k := (Pi.basisFun k (Fin n)).toMatrix b'
  have hPi : Invertible P := Basis.invertibleToMatrix (Pi.basisFun k (Fin n)) b'
  let Pu : GL (Fin n) k := unitOfInvertible P
  refine ⟨Pu⁻¹, fun x hx i j hij => ?_⟩
  have hcol : ∀ j : Fin n, ((x : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ
      (b' j) = μ ⟨x, hx⟩ ((finCongr (Module.finrank_fin_fun k)).symm j) • b' j := fun j => by
    have := hb' ⟨x, hx⟩ j
    simpa [f] using this
  have hxP : ((x : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) * P =
      P * diagonal (fun j => μ ⟨x, hx⟩ ((finCongr (Module.finrank_fin_fun k)).symm j)) := by
    ext a j
    have h := congrFun (hcol j) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_diagonal]
    simp only [P, Matrix.mul_apply, Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [h, mul_comm]
  have h1 : ((Pu⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = ⅟P := rfl
  have h2 : (((Pu⁻¹)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = P := by
    simp [Pu]
  rw [h1, h2, Matrix.mul_assoc, hxP, ← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul,
    diagonal_apply_ne _ hij]

end CFSG.RankThree.PartOne

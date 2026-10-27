module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.Algebra.IsSimpleRing

public section

namespace CFSG.StandardType

open Matrix
open Module
open Polynomial

theorem exists_diagonalizing_basis {ι κ Ω : Type} [Fintype ι] [DecidableEq ι] [Finite κ] [Field Ω]
    [IsAlgClosed Ω] [CharP Ω 2] (X : κ → Matrix ι ι Ω) (hcomm : ∀ i j, X i * X j = X j * X i)
    (h3 : ∀ i, X i ^ 3 = 1) :
    ∃ (P : GL ι Ω) (w : κ → ι → Ω), (∀ i α, w i α ^ 3 = 1) ∧
      ∀ i, X i * (P : Matrix ι ι Ω) = (P : Matrix ι ι Ω) * diagonal (w i) := by
  classical
  let V := ι → Ω
  let f : κ → Module.End Ω V := fun i => Matrix.toLin' (X i)
  have hf_pow : ∀ i : κ, f i ^ 3 = 1 := by
    intro i
    have hM : (X i) ^ 3 = 1 := h3 i
    change (Matrix.toLin' (X i) : Module.End Ω V) ^ 3 = 1
    rw [← Matrix.toLin'_pow, hM, Matrix.toLin'_one]
    rfl
  have hf_semisimple : ∀ i : κ, (f i).IsSemisimple := by
    intro i
    have h3ne : (3 : Ω) ≠ 0 := by
      intro hzero
      exact absurd ((CharP.cast_eq_zero_iff Ω 2 3).mp hzero) (by norm_num)
    have hsep : (Polynomial.X ^ 3 - Polynomial.C (1 : Ω) : Polynomial Ω).Separable :=
      Polynomial.separable_X_pow_sub_C (1 : Ω) h3ne one_ne_zero
    have hsq : Squarefree (Polynomial.X ^ 3 - 1 : Polynomial Ω) := by
      simpa using hsep.squarefree
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq ?_
    rw [map_sub, map_pow, aeval_X, map_one, hf_pow i, sub_self]
  have hcommEnd : Pairwise fun i j : κ => Commute (f i) (f j) := by
    intro i j hij
    show f i * f j = f j * f i
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    change (Matrix.toLin' (X i)).comp (Matrix.toLin' (X j)) =
      (Matrix.toLin' (X j)).comp (Matrix.toLin' (X i))
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hcomm i j]
  have hmax : ∀ i : κ, ⨆ μ : Ω, (f i).maxGenEigenspace μ = ⊤ := by
    intro i
    have hfin := (hf_semisimple i).isFinitelySemisimple
    simp_rw [hfin.maxGenEigenspace_eq_eigenspace]
    exact (hf_semisimple i).iSup_eigenspace_eq_top
  have htop_max : ⨆ χ : κ → Ω, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f hcommEnd hmax
  have hind_max : iSupIndep fun χ : κ → Ω => ⨅ i, (f i).maxGenEigenspace (χ i) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f (fun i j φ => by
      rcases eq_or_ne i j with rfl | hij
      · exact Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) φ
      · exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcommEnd hij).symm φ)
  have hmge : ∀ (i : κ) (μ : Ω), (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    fun i μ => (hf_semisimple i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have htop : ⨆ χ : κ → Ω, ⨅ i, (f i).eigenspace (χ i) = ⊤ := by
    have h := htop_max
    simp_rw [hmge] at h
    exact h
  have hind : iSupIndep fun χ : κ → Ω => ⨅ i, (f i).eigenspace (χ i) := by
    have h := hind_max
    simp_rw [hmge] at h
    exact h
  let joint : (κ → Ω) → Submodule Ω V := fun χ => ⨅ i, (f i).eigenspace (χ i)
  have hdecomp : DirectSum.IsInternal joint :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let b' : Module.Basis (Σ χ : κ → Ω, Fin (finrank Ω (joint χ))) Ω V :=
    hdecomp.collectedBasis fun χ => Module.finBasis Ω (joint χ)
  letI : Fintype (Σ χ : κ → Ω, Fin (finrank Ω (joint χ))) :=
    FiniteDimensional.fintypeBasisIndex b'
  have hcard : Fintype.card (Σ χ : κ → Ω, Fin (finrank Ω (joint χ))) = Fintype.card ι := by
    have h1 : Fintype.card (Σ χ : κ → Ω, Fin (finrank Ω (joint χ))) = finrank Ω V :=
      (Module.finrank_eq_card_basis b').symm
    have h2 : finrank Ω V = Fintype.card ι := by
      change finrank Ω (ι → Ω) = Fintype.card ι
      rw [Module.finrank_fintype_fun_eq_card]
    exact h1.trans h2
  let e : (Σ χ : κ → Ω, Fin (finrank Ω (joint χ))) ≃ ι :=
    Fintype.equivOfCardEq hcard
  let b'' : Module.Basis ι Ω V := b'.reindex e
  let w : κ → ι → Ω := fun i α => (e.symm α).1 i
  have heigen : ∀ (i : κ) (α : ι), f i (b'' α) = w i α • b'' α := by
    intro i α
    have hmem : b'' α ∈ joint (e.symm α).1 := by
      have h := hdecomp.collectedBasis_mem (fun χ => Module.finBasis Ω (joint χ)) (e.symm α)
      change (b'.reindex e) α ∈ joint (e.symm α).1
      rw [Module.Basis.reindex_apply]
      exact h
    have hmem' : b'' α ∈ (f i).eigenspace ((e.symm α).1 i) := by
      have hji : b'' α ∈ ⨅ j : κ, (f j).eigenspace ((e.symm α).1 j) := by
        simpa only [joint] using hmem
      exact ((Submodule.mem_iInf (fun j : κ => (f j).eigenspace ((e.symm α).1 j))).mp hji) i
    rw [Module.End.mem_eigenspace_iff] at hmem'
    simpa only [w] using hmem'
  have hw3 : ∀ i α, w i α ^ 3 = 1 := by
    intro i α
    have hpow : (f i ^ 3) (b'' α) = w i α ^ 3 • b'' α := by
      have h : ∀ n : ℕ, (f i ^ n) (b'' α) = w i α ^ n • b'' α := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          conv_lhs => rw [pow_succ]
          rw [Module.End.mul_apply, heigen i α, map_smul, ih, smul_smul, pow_succ']
      exact h 3
    have h3' : (f i ^ 3) (b'' α) = b'' α := by rw [hf_pow i]; rfl
    rw [h3'] at hpow
    have hz : (w i α ^ 3 - 1) • b'' α = 0 := by
      rw [sub_smul, one_smul, ← hpow, sub_self]
    rcases (smul_eq_zero.mp hz) with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (b''.ne_zero α)
  let E : Module.Basis ι Ω V := Pi.basisFun Ω ι
  let A : Matrix ι ι Ω := E.toMatrix b''
  let B : Matrix ι ι Ω := b''.toMatrix E
  have hAB : A * B = 1 := by
    simp only [A, B, E]
    rw [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]
  have hBA : B * A = 1 := by
    simp only [A, B, E]
    rw [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]
  let P : GL ι Ω := ⟨A, B, hAB, hBA⟩
  refine ⟨P, w, hw3, ?_⟩
  intro i
  have hdiag : LinearMap.toMatrix b'' b'' (f i) = diagonal (w i) := by
    ext a b
    rw [LinearMap.toMatrix_apply, heigen i b, map_smul, Finsupp.smul_apply, smul_eq_mul,
      Module.Basis.repr_self]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [Matrix.diagonal, hab]
  have hchange := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b'' E b'' E (f i)
  have htoMa : LinearMap.toMatrix E E (f i) = X i := by
    simp only [E, f]
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  have hmain : B * X i * A = diagonal (w i) := by
    rw [htoMa, hdiag] at hchange
    exact hchange
  change X i * A = A * diagonal (w i)
  calc X i * A = (A * B) * (X i * A) := by rw [hAB, Matrix.one_mul]
    _ = A * (B * (X i * A)) := by rw [Matrix.mul_assoc]
    _ = A * (B * X i * A) := by rw [← Matrix.mul_assoc B (X i) A]
    _ = A * diagonal (w i) := by rw [hmain]

end CFSG.StandardType

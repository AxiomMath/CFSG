module

public import CFSG.LocalAnalysis.StandardType.SpFixedNorm
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

namespace SpFixed

open Matrix
open Module
open Polynomial
open CFSG.Open (StatedSp)

@[expose] noncomputable def matOver (F : Type) [Field F] (n : ℕ) (Ω : Type) [Field Ω]
    [Algebra F Ω] : StatedSp n F →* Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω :=
  (RingHom.mapMatrix (algebraMap F Ω)).toMonoidHom.comp (matHom F n)

variable {F : Type} [Field F] {n : ℕ} {Ω : Type} [Field Ω] [Algebra F Ω]

theorem matOver_apply (a : StatedSp n F) :
    matOver F n Ω a = (matHom F n a).map (algebraMap F Ω) :=
  rfl

theorem matOver_injective : Function.Injective (matOver F n Ω) := by
  have hmap : Function.Injective (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F =>
      (RingHom.mapMatrix (algebraMap F Ω)) M) := by
    intro M N hMN
    exact Matrix.map_injective (FaithfulSMul.algebraMap_injective F Ω)
      (by simpa only [RingHom.mapMatrix_apply] using hMN)
  intro a b h
  apply matHom_injective
  apply hmap
  exact h

structure WeightBasis (F : Type) [Field F] (n : ℕ) (Ω : Type) [Field Ω] [Algebra F Ω]
    (D : Subgroup (StatedSp n F)) [Fintype D] where
  P : GL (Fin n ⊕ Fin n) Ω
  w : D → Fin n ⊕ Fin n → Ω
  conj_eq : ∀ a : D,
    ((P⁻¹ : GL (Fin n ⊕ Fin n) Ω) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω) *
        matOver F n Ω (a : StatedSp n F) *
        (P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω) = diagonal (w a)

theorem exists_weightBasis [IsAlgClosed Ω] [CharP Ω 2] (D : Subgroup (StatedSp n F)) [Fintype D]
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hexp : ∀ a ∈ D, a ^ 3 = 1) :
    Nonempty (WeightBasis F n Ω D) := by
  classical
  let V := Fin n ⊕ Fin n → Ω
  let f : D → Module.End Ω V := fun a => Matrix.toLin' (matOver F n Ω (a : StatedSp n F))
  have hf_mul : ∀ a b : D, f (a * b) = f a * f b := by
    intro a b
    change Matrix.toLin' (matOver F n Ω ((a : StatedSp n F) * (b : StatedSp n F))) =
      Matrix.toLin' (matOver F n Ω (a : StatedSp n F)) *
        Matrix.toLin' (matOver F n Ω (b : StatedSp n F))
    rw [map_mul, Matrix.toLin'_mul]
    rfl
  have hf_pow : ∀ a : D, f a ^ 3 = 1 := by
    intro a
    have hMa : (matOver F n Ω (a : StatedSp n F)) ^ 3 = 1 := by
      rw [← map_pow, hexp (a : StatedSp n F) a.2, map_one]
    change (Matrix.toLin' (matOver F n Ω (a : StatedSp n F)) : Module.End Ω V) ^ 3 = 1
    rw [← Matrix.toLin'_pow, hMa, Matrix.toLin'_one]
    rfl
  have hf_semisimple : ∀ a : D, (f a).IsSemisimple := by
    intro a
    have h3 : (3 : Ω) ≠ 0 := by
      intro hzero
      exact absurd ((CharP.cast_eq_zero_iff Ω 2 3).mp hzero) (by norm_num)
    have hsep : (X ^ 3 - C (1 : Ω) : Polynomial Ω).Separable :=
      Polynomial.separable_X_pow_sub_C (1 : Ω) h3 one_ne_zero
    have hsq : Squarefree (X ^ 3 - 1 : Polynomial Ω) := by
      simpa using hsep.squarefree
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq ?_
    rw [map_sub, map_pow, aeval_X, map_one, hf_pow a, sub_self]
  have hcommEnd : Pairwise fun i j : D => Commute (f i) (f j) := by
    intro i j hij
    show f i * f j = f j * f i
    rw [← hf_mul i j, ← hf_mul j i]
    congr 1
    exact Subtype.ext (hcomm (i : StatedSp n F) i.2 (j : StatedSp n F) j.2)
  have hmax : ∀ a : D, ⨆ μ : Ω, (f a).maxGenEigenspace μ = ⊤ := by
    intro a
    have hfin := (hf_semisimple a).isFinitelySemisimple
    simp_rw [hfin.maxGenEigenspace_eq_eigenspace]
    exact (hf_semisimple a).iSup_eigenspace_eq_top
  have htop_max : ⨆ χ : D → Ω, ⨅ a, (f a).maxGenEigenspace (χ a) = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f hcommEnd hmax
  have hind_max : iSupIndep fun χ : D → Ω => ⨅ a, (f a).maxGenEigenspace (χ a) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f (fun i j φ => by
      rcases eq_or_ne i j with rfl | hij
      · exact Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) φ
      · exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcommEnd hij).symm φ)
  have hmge : ∀ (a : D) (μ : Ω), (f a).maxGenEigenspace μ = (f a).eigenspace μ :=
    fun a μ => (hf_semisimple a).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have htop : ⨆ χ : D → Ω, ⨅ a, (f a).eigenspace (χ a) = ⊤ := by
    have h := htop_max
    simp_rw [hmge] at h
    exact h
  have hind : iSupIndep fun χ : D → Ω => ⨅ a, (f a).eigenspace (χ a) := by
    have h := hind_max
    simp_rw [hmge] at h
    exact h
  let joint : (D → Ω) → Submodule Ω V := fun χ => ⨅ a, (f a).eigenspace (χ a)
  have hdecomp : DirectSum.IsInternal joint :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let b' : Module.Basis (Σ χ : D → Ω, Fin (finrank Ω (joint χ))) Ω V :=
    hdecomp.collectedBasis fun χ => Module.finBasis Ω (joint χ)
  letI : Fintype (Σ χ : D → Ω, Fin (finrank Ω (joint χ))) :=
    FiniteDimensional.fintypeBasisIndex b'
  have hcard : Fintype.card (Σ χ : D → Ω, Fin (finrank Ω (joint χ))) =
      Fintype.card (Fin n ⊕ Fin n) := by
    have h1 : Fintype.card (Σ χ : D → Ω, Fin (finrank Ω (joint χ))) = finrank Ω V :=
      (Module.finrank_eq_card_basis b').symm
    have h2 : finrank Ω V = Fintype.card (Fin n ⊕ Fin n) := by
      change finrank Ω (Fin n ⊕ Fin n → Ω) = Fintype.card (Fin n ⊕ Fin n)
      rw [Module.finrank_fintype_fun_eq_card]
    exact h1.trans h2
  let e : (Σ χ : D → Ω, Fin (finrank Ω (joint χ))) ≃ (Fin n ⊕ Fin n) :=
    Fintype.equivOfCardEq hcard
  let b'' : Module.Basis (Fin n ⊕ Fin n) Ω V := b'.reindex e
  let w : D → Fin n ⊕ Fin n → Ω := fun a i => (e.symm i).1 a
  have heigen : ∀ (a : D) (i : Fin n ⊕ Fin n), f a (b'' i) = w a i • b'' i := by
    intro a i
    have hmem : b'' i ∈ joint (e.symm i).1 := by
      have h := hdecomp.collectedBasis_mem (fun χ => Module.finBasis Ω (joint χ)) (e.symm i)
      change (b'.reindex e) i ∈ joint (e.symm i).1
      rw [Module.Basis.reindex_apply]
      exact h
    have hmem' : b'' i ∈ (f a).eigenspace ((e.symm i).1 a) := by
      have hji : b'' i ∈ ⨅ b : D, (f b).eigenspace ((e.symm i).1 b) := by
        simpa only [joint] using hmem
      exact ((Submodule.mem_iInf (fun b : D => (f b).eigenspace ((e.symm i).1 b))).mp hji) a
    rw [Module.End.mem_eigenspace_iff] at hmem'
    simpa only [w] using hmem'
  have hmulvec : ∀ (a : D) (j : Fin n ⊕ Fin n),
      matOver F n Ω (a : StatedSp n F) *ᵥ b'' j = w a j • b'' j := by
    intro a j
    have h : (Matrix.toLin' (matOver F n Ω (a : StatedSp n F))) (b'' j) = w a j • b'' j :=
      heigen a j
    rwa [Matrix.toLin'_apply] at h
  have hdiag : ∀ a : D, LinearMap.toMatrix b'' b'' (f a) = diagonal (w a) := by
    intro a
    ext i j
    rw [LinearMap.toMatrix_apply, heigen a j, map_smul, Finsupp.smul_apply, smul_eq_mul,
      Module.Basis.repr_self]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal, hij]
  let E : Module.Basis (Fin n ⊕ Fin n) Ω V := Pi.basisFun Ω (Fin n ⊕ Fin n)
  let A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω := E.toMatrix b''
  let B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω := b''.toMatrix E
  have hAB : A * B = 1 := by
    simp only [A, B, E]
    rw [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]
  have hBA : B * A = 1 := by
    simp only [A, B, E]
    rw [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]
  let P : GL (Fin n ⊕ Fin n) Ω := ⟨A, B, hAB, hBA⟩
  refine ⟨P, w, ?_⟩
  intro a
  have hchange := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b'' E b'' E (f a)
  have htoMa : LinearMap.toMatrix E E (f a) = matOver F n Ω (a : StatedSp n F) := by
    simp only [E, f]
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  have hmain : B * matOver F n Ω (a : StatedSp n F) * A = diagonal (w a) := by
    rw [htoMa, hdiag a] at hchange
    exact hchange
  show B * matOver F n Ω (a : StatedSp n F) * A = diagonal (w a)
  exact hmain

end SpFixed

end CFSG.StandardType

module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

public section

namespace CFSG.RankThree.PartOne.KFK0

open Matrix Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]

@[expose] noncomputable def projPoly (p : ℕ) (μ : F) : F[X] :=
  haveI := Classical.decEq F
  ∏ ν ∈ (nthRootsFinset p (1 : F)).erase μ, (X - C ν)

theorem sub_mul_projPoly {p : ℕ} (hp : 0 < p) {ζ : F} (hζ : IsPrimitiveRoot ζ p) {μ : F}
    (hμ : μ ^ p = 1) : (X - C μ) * projPoly p μ = X ^ p - 1 := by
  classical
  have hmem : μ ∈ nthRootsFinset p (1 : F) := (mem_nthRootsFinset hp 1).2 hμ
  rw [projPoly, X_pow_sub_one_eq_prod hp hζ]
  convert Finset.mul_prod_erase (nthRootsFinset p (1 : F)) (fun ν => (X - C ν : F[X])) hmem using 3

theorem sub_mul_aeval_projPoly {p : ℕ} (hp : 0 < p) {ζ : F} (hζ : IsPrimitiveRoot ζ p) {μ : F}
    (hμ : μ ^ p = 1) {M : Matrix n n F} (hM : M ^ p = 1) :
    (M - μ • (1 : Matrix n n F)) * Polynomial.aeval M (projPoly p μ) = 0 := by
  have h := congrArg (Polynomial.aeval M) (sub_mul_projPoly hp hζ hμ)
  simp only [map_mul, map_sub, map_pow, aeval_X, map_one, aeval_C, hM, sub_self] at h
  rw [Algebra.algebraMap_eq_smul_one] at h
  exact h

theorem isUnit_aeval_prod {M : Matrix n n F} (s : Finset F)
    (hs : ∀ ν ∈ s, IsUnit (M - ν • (1 : Matrix n n F))) :
    IsUnit (Polynomial.aeval M (∏ ν ∈ s, (X - C ν : F[X]))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, map_mul]
    refine IsUnit.mul ?_ (ih fun ν hν => hs ν (Finset.mem_insert_of_mem hν))
    have := hs a (Finset.mem_insert_self a s)
    simpa [Algebra.algebraMap_eq_smul_one] using this

theorem exists_eigenvector_of_pow_eq_one {p : ℕ} (hp : 0 < p) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {M : Matrix n n F} (hM : M ^ p = 1) (hM1 : M ≠ 1) :
    ∃ ν : F, ν ^ p = 1 ∧ ν ≠ 1 ∧ ∃ v : n → F, v ≠ 0 ∧ M.mulVec v = ν • v := by
  classical
  by_contra hno
  push Not at hno
  have h1 : (1 : F) ∈ nthRootsFinset p (1 : F) := (mem_nthRootsFinset hp 1).2 (one_pow p)
  have hQ : ∀ ν ∈ (nthRootsFinset p (1 : F)).erase 1, IsUnit (M - ν • (1 : Matrix n n F)) := by
    intro ν hν
    obtain ⟨hν1, hν⟩ := Finset.mem_erase.1 hν
    rw [mem_nthRootsFinset hp] at hν
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro hdet0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
    refine hno ν hν hν1 v hv0 ?_
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  have hu := isUnit_aeval_prod (M := M) _ hQ
  have h0 := sub_mul_aeval_projPoly hp hζ (μ := 1) (one_pow p) hM
  rw [one_smul] at h0
  have : M - 1 = 0 := (hu.mul_left_eq_zero).1 h0
  exact hM1 (sub_eq_zero.1 this)

end CFSG.RankThree.PartOne.KFK0

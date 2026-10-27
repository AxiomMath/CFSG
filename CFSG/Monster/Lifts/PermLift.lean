module

public import CFSG.Monster.CodeAut.Perm
public import CFSG.Monster.Spin.FourierPauli
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.BilinearForm

public noncomputable section

namespace CFSG.Monster.Lifts

open CFSG.Monster.Code CFSG.Monster.Spin Matrix

@[expose] def permC (p : AutPerm) : C ≃ₗ[ZMod 2] C where
  toFun u := ⟨permWord p u, permWord_mem_of_mem_AutPerm p.2 u.2⟩
  invFun u := ⟨permWord (p⁻¹ : AutPerm) u, permWord_mem_of_mem_AutPerm (p⁻¹).2 u.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv u := Subtype.ext (funext fun i => by simp [permWord])
  right_inv u := Subtype.ext (funext fun i => by simp [permWord])

@[simp] theorem coe_permC (p : AutPerm) (u : C) :
    (permC p u : Fin 24 → ZMod 2) = permWord p u := rfl

@[expose] def betaP (p : AutPerm) (a b : C) : ZMod 2 := θ (permC p a) (permC p b) + θ a b

@[expose] def kappaP (p : AutPerm) (a : C) : ZMod 2 :=
  ∑ i, ∑ j, if i < j then basisC.repr a i * basisC.repr a j * betaP p (basisC i) (basisC j)
    else 0

theorem kappaP_sum (p : AutPerm) (μ : Fin 12 → ZMod 2) :
    kappaP p (∑ i, μ i • basisC i) =
      ∑ i, ∑ j, if i < j then μ i * μ j * betaP p (basisC i) (basisC j) else 0 := by
  rw [kappaP, basisC.repr_sum_self]

@[expose] def sLin (p : AutPerm) : (SpinIdx → ℚ) →ₗ[ℚ] SpinIdx → ℚ :=
  Fbasis.constr ℚ fun u => sgn (kappaP p u) • Fvec (permC p u)

@[expose] def smat (p : AutPerm) : Matrix SpinIdx SpinIdx ℚ := (LinearMap.toMatrix' (sLin p))ᵀ

theorem vecMul_smat (p : AutPerm) (v : SpinIdx → ℚ) : v ᵥ* smat p = sLin p v := by
  rw [smat, vecMul_transpose, LinearMap.toMatrix'_mulVec]

theorem Fvec_vecMul_smat (p : AutPerm) (u : C) :
    Fvec u ᵥ* smat p = sgn (kappaP p u) • Fvec (permC p u) := by
  have h := Fbasis.constr_basis ℚ (fun u => sgn (kappaP p u) • Fvec (permC p u)) u
  rw [coe_Fbasis] at h
  rw [vecMul_smat, sLin, h]

theorem eq_smat_of_forall {p : AutPerm} {M : Matrix SpinIdx SpinIdx ℚ}
    (h : ∀ u : C, Fvec u ᵥ* M = sgn (kappaP p u) • Fvec (permC p u)) : M = smat p := by
  have key : toLin' Mᵀ = toLin' (smat p)ᵀ := by
    refine Fbasis.ext fun u => ?_
    rw [toLin'_apply, toLin'_apply, mulVec_transpose, mulVec_transpose, coe_Fbasis, h,
      Fvec_vecMul_smat]
  have := congrArg transpose (toLin'.injective key)
  rwa [transpose_transpose, transpose_transpose] at this

theorem smat_mul_transpose_self (p : AutPerm) : smat p * (smat p)ᵀ = 1 := by
  apply toBilin'.injective
  refine LinearMap.BilinForm.ext_basis Fbasis fun u v => ?_
  rw [toBilin'_apply', toBilin'_apply', ← mulVec_mulVec, mulVec_transpose, dotProduct_mulVec,
    one_mulVec, coe_Fbasis, Fvec_vecMul_smat, Fvec_vecMul_smat, smul_dotProduct, dotProduct_smul,
    Fvec_dotProduct_Fvec, Fvec_dotProduct_Fvec]
  simp only [(permC p).injective.eq_iff]
  split_ifs with huv
  · subst huv
    have hs : sgn (kappaP p u) * sgn (kappaP p u) = 1 := sgnR_mul_self (R := ℚ) _
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, hs, one_mul]
  · simp

theorem smat_transpose_mul_self (p : AutPerm) : (smat p)ᵀ * smat p = 1 :=
  mul_eq_one_comm.1 (smat_mul_transpose_self p)

@[expose] def sU (p : AutPerm) : GL SpinIdx ℚ :=
  ⟨smat p, (smat p)ᵀ, smat_mul_transpose_self p, smat_transpose_mul_self p⟩

@[simp] theorem coe_sU (p : AutPerm) : (sU p : Matrix SpinIdx SpinIdx ℚ) = smat p := rfl

@[expose] def Pmat (p : Equiv.Perm (Fin 24)) : Matrix (Fin 24) (Fin 24) ℚ := p.permMatrix ℚ

theorem vecMul_Pmat (p : Equiv.Perm (Fin 24)) (v : Fin 24 → ℚ) : v ᵥ* Pmat p = v ∘ ⇑p⁻¹ :=
  vecMul_permMatrix p

theorem single_vecMul_Pmat (p : Equiv.Perm (Fin 24)) (i : Fin 24) :
    Pi.single i 1 ᵥ* Pmat p = Pi.single (p i) 1 := by
  rw [vecMul_Pmat]
  funext j
  simp only [Function.comp_apply, Pi.single_apply, Equiv.Perm.inv_eq_iff_eq]

theorem Pmat_mul (p q : Equiv.Perm (Fin 24)) : Pmat (q * p) = Pmat p * Pmat q :=
  permMatrix_mul q p

theorem Pmat_transpose (p : Equiv.Perm (Fin 24)) : (Pmat p)ᵀ = Pmat p⁻¹ :=
  transpose_permMatrix p

theorem Pmat_mul_transpose_self (p : Equiv.Perm (Fin 24)) : Pmat p * (Pmat p)ᵀ = 1 := by
  rw [Pmat_transpose, ← Pmat_mul, inv_mul_cancel, Pmat, permMatrix_one]

theorem Pmat_transpose_mul_self (p : Equiv.Perm (Fin 24)) : (Pmat p)ᵀ * Pmat p = 1 := by
  rw [Pmat_transpose, ← Pmat_mul, mul_inv_cancel, Pmat, permMatrix_one]

@[expose] def PU (p : Equiv.Perm (Fin 24)) : GL (Fin 24) ℚ :=
  ⟨Pmat p, (Pmat p)ᵀ, Pmat_mul_transpose_self p, Pmat_transpose_mul_self p⟩

@[simp] theorem coe_PU (p : Equiv.Perm (Fin 24)) : (PU p : Matrix (Fin 24) (Fin 24) ℚ) = Pmat p :=
  rfl

theorem code_permutation_spin_lift_data :
    (∀ p : Equiv.Perm (Fin 24), p ∈ AutPerm ↔ ∀ x : Fin 24 → ZMod 2, x ∈ C ↔ permWord p x ∈ C) ∧
    (∀ (p : AutPerm) (u : C), (permC p u : Fin 24 → ZMod 2) = permWord p u) ∧
    (∀ (p : AutPerm) (a b : C), betaP p a b = θ (permC p a) (permC p b) + θ a b) ∧
    (∀ (p : AutPerm) (μ : Fin 12 → ZMod 2), kappaP p (∑ i, μ i • basisC i) =
      ∑ i, ∑ j, if i < j then μ i * μ j * betaP p (basisC i) (basisC j) else 0) ∧
    (∀ (p : AutPerm) (u : C), Fvec u ᵥ* smat p = sgn (kappaP p u) • Fvec (permC p u)) ∧
    (∀ (p : AutPerm) (M : Matrix SpinIdx SpinIdx ℚ),
      (∀ u : C, Fvec u ᵥ* M = sgn (kappaP p u) • Fvec (permC p u)) → M = smat p) ∧
    (∀ p : AutPerm, smat p * (smat p)ᵀ = 1 ∧ (smat p)ᵀ * smat p = 1) ∧
    (∀ (p : Equiv.Perm (Fin 24)) (i : Fin 24), Pi.single i 1 ᵥ* Pmat p = Pi.single (p i) 1) ∧
    (∀ (p : Equiv.Perm (Fin 24)) (v : Fin 24 → ℚ), v ᵥ* Pmat p = v ∘ ⇑p⁻¹) ∧
    (∀ p : Equiv.Perm (Fin 24), Pmat p * (Pmat p)ᵀ = 1 ∧ (Pmat p)ᵀ * Pmat p = 1) :=
  ⟨fun _ => mem_AutPerm_iff_permWord, coe_permC, fun _ _ _ => rfl, kappaP_sum, Fvec_vecMul_smat,
    fun _ _ h => eq_smat_of_forall h,
    fun p => ⟨smat_mul_transpose_self p, smat_transpose_mul_self p⟩, single_vecMul_Pmat,
    vecMul_Pmat, fun p => ⟨Pmat_mul_transpose_self p, Pmat_transpose_mul_self p⟩⟩

end CFSG.Monster.Lifts

module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K] {n : ℕ}

theorem signedPermutation_toGL_mem_normalizer_diagonalTorus (w : Equiv.Perm (Fin n)) :
    Matrix.SpecialLinearGroup.toGL (signedPermutation n K w) ∈
      Subgroup.normalizer (TauCeti.diagonalTorus K n : Set (GL (Fin n) K)) := by
  classical
  let s : Kˣ := Units.map (Int.castRingHom K) (Equiv.Perm.sign w)
  have hs : (s : K) = ((Equiv.Perm.sign w : ℤ) : K) := by simp [s]
  let d : Fin n → Kˣ := fun i => if (i : ℕ) = 0 then s else 1
  have hd : ∀ i : Fin n,
      (d i : K) = if (i : ℕ) = 0 then ((Equiv.Perm.sign w : ℤ) : K) else 1 := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · simp [d, hi, hs]
    · simp [d, hi]
  have hfun : (fun a : Fin n => if (a : ℕ) = 0 then ((Equiv.Perm.sign w : ℤ) : K) else 1) =
      fun a => (d a : K) := funext fun a => (hd a).symm
  have hmono : Matrix.SpecialLinearGroup.toGL (signedPermutation n K w) =
      TauCeti.diagGL d * TauCeti.permutationGL (k := K) w := by
    refine Units.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Units.val_mul, TauCeti.diagGL_coe,
      TauCeti.permutationGL_coe, coe_signedPermutation]
    simp only [signedPermMatrix, permMatrix_eq, hfun]
  rw [hmono]
  exact Subgroup.mul_mem _
    (Subgroup.le_normalizer (TauCeti.mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, rfl⟩))
    (TauCeti.permutationGL_mem_normalizer w)

theorem projUnitriangular_sup_comap_normalizer_eq_top :
    projUnitriangular n K ⊔ (normalizer (((TauCeti.diagonalTorus K n).map (conjAut n K) :
      Subgroup (MulAut (projectiveSL n K))) : Set (MulAut (projectiveSL n K)))).comap
        (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)) = ⊤ := by
  classical
  have hconj_mem : ∀ m : Matrix.SpecialLinearGroup (Fin n) K,
      Matrix.SpecialLinearGroup.toGL m ∈ Subgroup.normalizer (TauCeti.diagonalTorus K n :
        Set (GL (Fin n) K)) →
      MulAut.conj (proj n K m) ∈ Subgroup.normalizer
        (((TauCeti.diagonalTorus K n).map (conjAut n K) : Subgroup (MulAut (projectiveSL n K))) :
          Set (MulAut (projectiveSL n K))) := by
    intro m hm
    rw [← conjAut_toGL]
    exact Subgroup.le_normalizer_map (conjAut n K) (Subgroup.mem_map_of_mem (conjAut n K) hm)
  have hdiag : ∀ d : Matrix.SpecialLinearGroup (Fin n) K,
      (d : Matrix (Fin n) (Fin n) K).IsDiag →
      proj n K d ∈ (Subgroup.normalizer (((TauCeti.diagonalTorus K n).map (conjAut n K) :
        Subgroup (MulAut (projectiveSL n K))) : Set (MulAut (projectiveSL n K)))).comap
          (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)) := by
    intro d hd
    rw [Subgroup.mem_comap]
    exact hconj_mem d (Subgroup.le_normalizer (TauCeti.mem_diagonalTorus_iff.mpr hd))
  have hsigned : ∀ w : Equiv.Perm (Fin n),
      proj n K (signedPermutation n K w) ∈ (Subgroup.normalizer
        (((TauCeti.diagonalTorus K n).map (conjAut n K) : Subgroup (MulAut (projectiveSL n K))) :
          Set (MulAut (projectiveSL n K)))).comap
          (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)) := by
    intro w
    rw [Subgroup.mem_comap]
    exact hconj_mem _ (signedPermutation_toGL_mem_normalizer_diagonalTorus w)
  rw [Subgroup.eq_top_iff']
  intro x
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell g
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.mp hw
  obtain ⟨u₁, hu₁, d₁, hd₁, rfl⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.exists_unitriangular_mul_diagonal hb₁
  obtain ⟨u₂, hu₂, d₂, hd₂, rfl⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.exists_unitriangular_mul_diagonal hb₂
  have hkey : proj n K (u₁ * d₁ * signedPermutation n K w * (u₂ * d₂)) =
      proj n K u₁ * proj n K d₁ * proj n K (signedPermutation n K w) *
        (proj n K u₂ * proj n K d₂) := by
    simp only [map_mul]
  rw [hkey]
  exact mul_mem (mul_mem (mul_mem
    (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem (proj n K) hu₁))
    (Subgroup.mem_sup_right (hdiag d₁ hd₁)))
    (Subgroup.mem_sup_right (hsigned w)))
    (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem (proj n K) hu₂))
      (Subgroup.mem_sup_right (hdiag d₂ hd₂)))

theorem conjAut_mem_projUnitriangular_iff {u : GL (Fin n) K}
    (hu : u ∈ TauCeti.upperUnitriangularGroup (Fin n) K) (w : projectiveSL n K) :
    conjAut n K u w ∈ projUnitriangular n K ↔ w ∈ projUnitriangular n K := by
  have htri : (u : Matrix (Fin n) (Fin n) K).IsUpperUnitriangular :=
    TauCeti.UpperUnitriangularGroup.mem_iff.mp hu
  have hdet : (u : Matrix (Fin n) (Fin n) K).det = 1 := htri.det_eq_one
  let u' : Matrix.SpecialLinearGroup (Fin n) K := ⟨(u : Matrix (Fin n) (Fin n) K), hdet⟩
  have hu' : Matrix.SpecialLinearGroup.toGL u' = u := Units.ext rfl
  have hmem : u' ∈ unitriangular n K := by
    rw [mem_unitriangular]
    exact ⟨fun _ _ hij => htri.isUpperTriangular hij, fun i => htri.apply_diag i⟩
  have hconj : conjAut n K u = MulAut.conj (proj n K u') := by
    rw [← hu', conjAut_toGL]
  have hproj : proj n K u' ∈ projUnitriangular n K :=
    Subgroup.mem_map_of_mem (proj n K) hmem
  rw [hconj, MulAut.conj_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : (proj n K u')⁻¹ * (proj n K u' * w * (proj n K u')⁻¹) * (proj n K u') ∈
        projUnitriangular n K := mul_mem (mul_mem (inv_mem hproj) h) hproj
    have h2 : (proj n K u')⁻¹ * (proj n K u' * w * (proj n K u')⁻¹) * (proj n K u') = w := by
      group
    rwa [h2] at h1
  · exact mul_mem (mul_mem hproj h) (inv_mem hproj)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

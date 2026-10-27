module

public import CFSG.RankThree.PartOne.KF4.B2Orbit

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.ClassicalGroups.Alternating CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

section Form

variable {K : Type} [Field K]

variable (K) in
abbrev f4B2Form : LinearMap.BilinForm K (Fin 4 → K) := Matrix.toBilin' (f4B2J0 K)

theorem f4B2Form_apply (x y : Fin 4 → K) :
    f4B2Form K x y = x 0 * y 3 - x 1 * y 2 + x 2 * y 1 - x 3 * y 0 := by
  simp [f4B2Form, Matrix.toBilin'_apply', f4B2J0, dotProduct, Matrix.mulVec, Fin.sum_univ_four]
  ring

theorem f4B2Form_isAlt : (f4B2Form K).IsAlt := fun x => by
  rw [f4B2Form_apply]; ring

theorem f4B2Form_nondegenerate : (f4B2Form K).Nondegenerate := by
  refine LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr ?_
  have h : f4B2J0 K * (-f4B2J0 K) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [f4B2J0, Matrix.mul_apply, Fin.sum_univ_four]
  exact (Matrix.isUnit_det_of_right_inverse h).ne_zero

theorem mem_f4SpGroup_iff_toLin (A : GL (Fin 4) K) :
    A ∈ f4SpGroup K ↔
      Matrix.GeneralLinearGroup.toLin A ∈ bilinIsometryGroup (f4B2Form K) := by
  have key : ∀ x y : Fin 4 → K,
      f4B2Form K ((A : Matrix (Fin 4) (Fin 4) K) *ᵥ x) ((A : Matrix (Fin 4) (Fin 4) K) *ᵥ y) =
      (Matrix.toBilin' ((A : Matrix (Fin 4) (Fin 4) K)ᵀ * f4B2J0 K *
        (A : Matrix (Fin 4) (Fin 4) K))) x y := by
    intro x y
    rw [← Matrix.toBilin'_comp]
    rfl
  constructor
  · intro h x y
    have := key x y
    rw [mem_f4SpGroup.1 h] at this
    exact this
  · intro h
    rw [mem_f4SpGroup]
    apply Matrix.toBilin'.injective
    refine LinearMap.ext₂ fun x y => ?_
    rw [← key x y]
    exact h x y

theorem toLin_apply (g : GL (Fin 4) K) (x : Fin 4 → K) :
    ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup K (Fin 4 → K)) :
      (Fin 4 → K) →ₗ[K] (Fin 4 → K)) x = (g : Matrix (Fin 4) (Fin 4) K) *ᵥ x :=
  rfl

theorem symplecticTransvection_conj {V : Type*} [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} (hB : B.IsAlt) {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ bilinIsometryGroup B) (a : V) (c : K) :
    g * symplecticTransvection B hB a c * g⁻¹ =
      symplecticTransvection B hB ((g : V →ₗ[K] V) a) c := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  have h1 : (g : V →ₗ[K] V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x) = x := by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  have h2 : B (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x) a =
      B x ((g : V →ₗ[K] V) a) := by
    rw [← hg (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x) a, h1]
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
    symplecticTransvection_apply, symplecticTransvection_apply, map_add, map_smul, h1, h2]

end Form

section Surj

variable
  {K : Type} [Field K]

theorem f4B2_transvection_e1 (c : K) :
    ∃ g ∈ f4B2Range K, Matrix.GeneralLinearGroup.toLin g =
      symplecticTransvection (f4B2Form K) f4B2Form_isAlt (Pi.single 1 1) c := by
  obtain ⟨g, hg, hgc⟩ := memR_x2 c
  refine ⟨g, hg, Units.ext (LinearMap.ext fun x => ?_)⟩
  rw [toLin_apply, hgc, symplecticTransvection_apply, f4B2Form_apply]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply,
      Matrix.one_apply]

theorem f4SpGroup_le_range : f4SpGroup K ≤ f4B2Range K := by
  intro A hA
  have hA' := (mem_f4SpGroup_iff_toLin A).1 hA
  rw [alternating_transvection_generation f4B2Form_isAlt f4B2Form_nondegenerate] at hA'
  have hcl : Subgroup.closure {g | ∃ (a : Fin 4 → K) (c : K),
      g = symplecticTransvection (f4B2Form K) f4B2Form_isAlt a c} ≤
      (f4B2Range K).map Matrix.GeneralLinearGroup.toLin.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨a, c, rfl⟩
    by_cases ha : a = 0
    · subst ha
      rw [show symplecticTransvection (f4B2Form K) f4B2Form_isAlt 0 c = 1 from by
        refine Units.ext (LinearMap.ext fun x => ?_)
        rw [symplecticTransvection_apply, smul_zero, add_zero]
        rfl]
      exact one_mem _
    · obtain ⟨M, ⟨g, hg, rfl⟩, hMa⟩ := exists_mem_range_mulVec ha
      obtain ⟨t, ht, htc⟩ := f4B2_transvection_e1 (K := K) c
      have hgiso : Matrix.GeneralLinearGroup.toLin g ∈ bilinIsometryGroup (f4B2Form K) :=
        (mem_f4SpGroup_iff_toLin g).1 (by
          obtain ⟨q, rfl⟩ := hg
          exact (f4B2Rep K q).2)
      have hconj := symplecticTransvection_conj f4B2Form_isAlt hgiso (Pi.single 1 1) c
      have hga : ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup K (Fin 4 → K)) :
          (Fin 4 → K) →ₗ[K] (Fin 4 → K)) (Pi.single 1 1) = a := by
        rw [toLin_apply]
        exact hMa
      rw [hga, ← htc] at hconj
      rw [← hconj]
      exact ⟨g * t * g⁻¹, mul_mem (mul_mem hg ht) (inv_mem hg), by simp⟩
  obtain ⟨g, hg, hgA⟩ := hcl hA'
  have : g = A := Matrix.GeneralLinearGroup.toLin.injective hgA
  exact this ▸ hg

theorem f4B2Rep_surjective : Function.Surjective (f4B2Rep K) := by
  rintro ⟨A, hA⟩
  obtain ⟨q, hq⟩ := f4SpGroup_le_range hA
  exact ⟨q, Subtype.ext hq⟩

variable (K) in
@[expose] def f4B2Equiv : subsystemGroup Tag.F4 K f4B2Support ≃* f4SpGroup K :=
  MulEquiv.ofBijective (f4B2Rep K) ⟨f4B2Rep_injective, f4B2Rep_surjective⟩

theorem coe_f4B2Equiv (g : subsystemGroup Tag.F4 K f4B2Support) :
    (((f4B2Equiv K g : f4SpGroup K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      f4B2_data.Mat (g : ModGL Tag.F4 K) :=
  rfl

end Surj

end CFSG.RankThree.PartOne.KF4

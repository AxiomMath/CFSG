module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.CubeFix

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open CFSG.RankThree.GF2n.Smith81

theorem isTransvec_eL_of_isConj {X : Type} [Group X] (S : CubeSetting X) {x : X} (hx : x ∈ S.L)
    (hconj : IsConj S.z x) : IsTransvec (S.eL ⟨x, hx⟩) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  let zx : ↥S.L := ⟨x, hx⟩
  let z' : ↥S.L := S.eL.symm CFSG.Holt.SL6.stdTransvection
  have hz'eL : S.eL z' = CFSG.Holt.SL6.stdTransvection :=
    MulEquiv.apply_symm_apply S.eL _
  have hρx_cube : S.ρ x = cubeAct (S.eL zx) := S.hρ zx
  have hρz : S.ρ S.z = cubeAct CFSG.Holt.SL6.stdTransvection := by
    have h := S.hρ z'
    rw [hz'eL] at h
    exact h
  have hρx : S.ρ x = S.ρ c * S.ρ S.z * S.ρ (c⁻¹) := by
    rw [← hc, map_mul, map_mul]
  have hE : S.ρ c * S.ρ (c⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hE' : S.ρ (c⁻¹) * S.ρ c = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hE'_apply : ∀ v, S.ρ (c⁻¹) (S.ρ c v) = v := by
    intro v
    rw [← Module.End.mul_apply, hE', Module.End.one_apply]
  have hE_apply : ∀ v, S.ρ c (S.ρ (c⁻¹) v) = v := by
    intro v
    rw [← Module.End.mul_apply, hE, Module.End.one_apply]
  have hE_inj : Function.Injective (S.ρ c) := by
    intro u v huv
    have h1 := hE'_apply u
    have h2 := hE'_apply v
    rw [huv] at h1
    rw [h1] at h2
    exact h2
  have hsub : S.ρ x - 1 = S.ρ c * (S.ρ S.z - 1) * S.ρ (c⁻¹) := by
    apply LinearMap.ext
    intro v
    simp only [hρx, LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply,
      LinearMap.map_sub, hE_apply]
  let φ : LinearMap.ker (S.ρ S.z - 1) →ₗ[ZMod 2] LinearMap.ker (S.ρ x - 1) :=
    (S.ρ c).restrict fun w hw => by
      rw [LinearMap.mem_ker, hsub]
      simp only [Module.End.mul_apply]
      rw [hE'_apply w, LinearMap.mem_ker.mp hw, map_zero]
  have hφ : Function.Bijective φ := by
    constructor
    · intro u v huv
      apply Subtype.ext
      apply hE_inj
      exact congrArg Subtype.val huv
    · intro v
      refine ⟨⟨S.ρ (c⁻¹) v, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker]
        apply hE_inj
        rw [map_zero]
        have h5 : (S.ρ c * (S.ρ S.z - 1) * S.ρ (c⁻¹)) (v : A5Cube.Cube (ZMod 2)) = 0 := by
          have h6 := congrArg (fun T => T (v : A5Cube.Cube (ZMod 2))) hsub
          rw [← h6]
          exact LinearMap.mem_ker.mp v.2
        simpa only [Module.End.mul_apply] using h5
      · apply Subtype.ext
        show S.ρ c (S.ρ (c⁻¹) v) = v
        rw [← Module.End.mul_apply, hE, Module.End.one_apply]
  have hdim : fixedDim (S.ρ x) = fixedDim (S.ρ S.z) :=
    (LinearEquiv.ofBijective φ hφ).finrank_eq.symm
  have hle : 14 ≤ fixedDim (cubeAct (S.eL zx)) := by
    calc 14 ≤ fixedDim (cubeAct CFSG.Holt.SL6.stdTransvection) :=
          le_fixedDim_cubeAct_stdTransvection
      _ = fixedDim (S.ρ S.z) := by rw [hρz]
      _ = fixedDim (cubeAct (S.eL zx)) := by rw [hdim.symm, hρx_cube]
  have hstd_sq : CFSG.Holt.SL6.stdTransvection * CFSG.Holt.SL6.stdTransvection = 1 := by
    have h := Matrix.SpecialLinearGroup.transvection_mul_neg (i := (0 : Fin 6)) (j := 5)
      (by decide) (1 : ZMod 2)
    simpa [CFSG.Holt.SL6.stdTransvection] using h
  have hstd_ne : CFSG.Holt.SL6.stdTransvection ≠ 1 := by
    intro h
    have hmem : CFSG.Holt.SL6.stdTransvection ∈ Subgroup.center (SL(6, ZMod 2)) := by
      rw [h]
      exact Subgroup.mem_center_iff.mpr fun g => by simp
    have h10 : (1 : ZMod 2) = 0 := by
      refine (Matrix.SpecialLinearGroup.transvection_mem_center_iff (i := (0 : Fin 6)) (j := 5)
        (by decide) (1 : ZMod 2)).mp ?_
      simpa [CFSG.Holt.SL6.stdTransvection] using hmem
    exact one_ne_zero h10
  have hz'_ne : z' ≠ 1 := by
    intro h1
    apply hstd_ne
    rw [← hz'eL, h1, map_one]
  have hz_sq : S.z * S.z = 1 := by
    have h : z' * z' = 1 := by
      apply S.eL.injective
      rw [map_mul, hz'eL, hstd_sq, map_one]
    rw [show S.z = (z' : X) from rfl]
    exact congrArg (fun t : ↥S.L => (t : X)) h
  have hz_ne : S.z ≠ 1 := by
    rw [show S.z = (z' : X) from rfl]
    intro h
    exact hz'_ne (Subtype.ext h)
  have hx_sq : x * x = 1 := by
    rw [← hc]
    have h : c * S.z * c⁻¹ * (c * S.z * c⁻¹) = c * (S.z * S.z) * c⁻¹ := by group
    rw [h, hz_sq, mul_one, mul_inv_cancel]
  have hx_ne : x ≠ 1 := by
    intro h
    have hz1 : S.z = 1 := by
      have h' := congrArg (fun t => c⁻¹ * t * c) (hc.trans h)
      group at h'
      exact h'
    exact hz_ne hz1
  have hzx_sq : S.eL zx * S.eL zx = 1 := by
    have hzz : zx * zx = 1 := Subtype.ext hx_sq
    rw [← map_mul, hzz, map_one]
  have hzx_ne : S.eL zx ≠ 1 := by
    intro h
    apply hx_ne
    have h1 : zx = 1 := S.eL.injective (by rw [h, map_one])
    exact Subtype.ext_iff.mp h1
  exact isTransvec_of_le_fixedDim_cubeAct hzx_sq hzx_ne hle

end CFSG.StandardType.FF81.CentE6

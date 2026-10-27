module

public import CFSG.Monster.B.Cbar.SignedSum
public import CFSG.Monster.Griess.AutFinite

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Parity Matrix

@[expose] noncomputable def unitB : SpaceB := inA ((4 : ℚ)⁻¹ • oneA)

theorem qf_smul_one (c : ShortIdx) (t : ℚ) :
    qf c (t • (1 : Matrix (Fin 24) (Fin 24) ℚ)) = 32 * t := by
  rw [qf_smul, qf, Matrix.one_mulVec, uQ_dotProduct_uQ_self]
  ring

theorem gmul_unitB (v : SpaceB) : gmul unitB v = v := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (funext fun c => ?_) ?_)
  · change gmulA unitB v = Am v
    simp only [gmulA, unitB, Am_inA, xs_inA, Nm_inA, Pi.zero_apply, zero_mul, zero_smul,
      Finset.sum_const_zero, smul_zero, add_zero, transpose_zero, Matrix.zero_mul, trace_zero,
      zero_div, Matrix.mul_zero, coe_smul_oneA, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    module
  · change gmulX unitB v c = xs v c
    simp only [gmulX, unitB, Am_inA, xs_inA, Nm_inA, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, transpose_zero, Matrix.zero_mul, trace_zero, qf_zero, zero_div,
      add_zero, coe_smul_oneA, qf_smul_one]
    ring
  · change gmulWHalf unitB v + gmulWHalf v unitB = Nm v
    simp only [gmulWHalf, unitB, Am_inA, xs_inA, Nm_inA, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, smul_zero, add_zero, Matrix.mul_zero, Matrix.zero_mul, sub_zero,
      coe_smul_oneA, trace_smul, trace_one, Fintype.card_fin, Matrix.mul_smul, Matrix.mul_one,
      smul_eq_mul]
    module

theorem inA_oneA_eq : inA oneA = (4 : ℚ) • unitB := by
  rw [unitB, Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero, smul_smul]
  norm_num

theorem AutO_apply_unitB {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO) : g unitB = unitB := by
  have hunit : ∀ w, gmul (g unitB) w = w := by
    intro w
    have h := (mem_AutO.1 hg).1 unitB (g.symm w)
    rw [gmul_unitB, LinearEquiv.apply_symm_apply] at h
    exact h.symm
  calc g unitB = gmul unitB (g unitB) := (gmul_unitB _).symm
    _ = gmul (g unitB) unitB := gmul_comm _ _
    _ = unitB := hunit unitB

theorem AutO_apply_inA_oneA {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO) :
    g (inA oneA) = inA oneA := by
  rw [inA_oneA_eq, map_smul, AutO_apply_unitB hg]

@[expose] noncomputable def traceVec (r : Q) : SpaceB := (1070 : ℚ) • inA oneA - (4096 : ℚ) • axis r

theorem trace_identity_transport {r s : Q} {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO)
    (hρ : g * rhoEquiv r * g⁻¹ = rhoEquiv s) (ha : g (axis r) = axis s)
    (H : ∀ v, LinearMap.trace ℚ SpaceB (rhoL r v) = bform (traceVec r) v) (v : SpaceB) :
    LinearMap.trace ℚ SpaceB (rhoL s v) = bform (traceVec s) v := by
  have hg' : g⁻¹ ∈ AutO := inv_mem hg
  have hconj : rhoL s v =
      (g : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ rhoL r (g.symm v) ∘ₗ ((g⁻¹ : SpaceB ≃ₗ[ℚ] SpaceB) :
        SpaceB →ₗ[ℚ] SpaceB) := by
    apply LinearMap.ext
    intro u
    rw [rhoL_apply, ← hρ, LinearMap.comp_apply, LinearMap.comp_apply, rhoL_apply]
    change g (rhoEquiv r (g⁻¹ (gmul v u))) = g (rhoEquiv r (gmul (g.symm v) (g⁻¹ u)))
    rw [(mem_AutO.1 hg').1 v u]
    rfl
  have htr : LinearMap.trace ℚ SpaceB (rhoL s v) =
      LinearMap.trace ℚ SpaceB (rhoL r (g.symm v)) := by
    rw [hconj, ← LinearMap.comp_assoc, LinearMap.trace_comp_comm', ← LinearMap.comp_assoc]
    have h1 : ((g⁻¹ : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ (g : SpaceB →ₗ[ℚ] SpaceB) =
        LinearMap.id := by
      apply LinearMap.ext
      intro u
      exact g.symm_apply_apply u
    rw [h1, LinearMap.id_comp]
  have hvec : g (traceVec r) = traceVec s := by
    rw [traceVec, traceVec, map_sub, map_smul, map_smul, AutO_apply_inA_oneA hg, ha]
  rw [htr, H, ← (mem_AutO.1 hg).2, hvec, LinearEquiv.apply_symm_apply]

theorem trace_rhoL_rStar (v : SpaceB) :
    LinearMap.trace ℚ SpaceB (rhoL (rMinus 0 1) v) = bform (traceVec (rMinus 0 1)) v :=
  trace_rhoL_of_signedU hrStar signedU_rStar v

end CFSG.Monster.B

module

public import CFSG.RankThree.PartOne.KC.UnitaryPlaneProjection
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import Mathlib.RingTheory.WittVector.IsPoly

public section

namespace CFSG.RankThree.PartOne.KCUnitaryPlane

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]
  {B : V →ₛₗ[σ] V →ₗ[K] K}

@[expose] def IsSelfAdj (B : V →ₛₗ[σ] V →ₗ[K] K) (E : Module.End K V) : Prop :=
  ∀ v w, B (E v) w = B v (E w)

section Group

variable {P : Type*} [Group P] (ρ : P →* LinearMap.GeneralLinearGroup K V)

theorem B_act_inv (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (x : P) (v w : V) :
    B (act ρ x v) w = B v (act ρ x⁻¹ w) := by
  have h : B (act ρ x v) (act ρ x (act ρ x⁻¹ w)) = B v (act ρ x⁻¹ w) := hρ x v (act ρ x⁻¹ w)
  rwa [act_inv_apply] at h

variable [Fintype P]

theorem sumOp_selfAdj (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (L : Subgroup P) :
    IsSelfAdj B (sumOp ρ L) := by
  classical
  intro v w
  unfold sumOp
  simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_equiv (Equiv.inv P) ?_ ?_
  · intro x
    simp [Finset.mem_filter]
  · intro x _
    simp only [Equiv.inv_apply]
    rw [B_act_inv ρ hρ]

theorem avgOp_selfAdj (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (L : Subgroup P) :
    IsSelfAdj B (avgOp ρ L) := by
  intro v w
  have h := sumOp_selfAdj ρ hρ L v w
  unfold avgOp
  simp only [LinearMap.smul_apply, map_smulₛₗ, h, map_inv₀, map_natCast, smul_eq_mul]

end Group

section Idempotent

variable {E : Module.End K V}

theorem orth_range_ker (hB : B.IsSymm) (hE : IsSelfAdj B E) {v w : V}
    (hv : v ∈ LinearMap.range E) (hw : w ∈ LinearMap.ker E) : B v w = 0 ∧ B w v = 0 := by
  obtain ⟨u, rfl⟩ := hv
  have h1 : B (E u) w = 0 := by
    rw [hE, LinearMap.mem_ker.mp hw, map_zero]
  refine ⟨h1, ?_⟩
  rw [← (LinearMap.isSymm_def.mp hB) (E u) w, h1, map_zero]

theorem sub_apply_mem_ker (hidem : E * E = E) (v : V) : v - E v ∈ LinearMap.ker E := by
  rw [LinearMap.mem_ker, map_sub]
  have := congrArg (fun f : Module.End K V => f v) hidem
  simp only [Module.End.mul_apply] at this
  rw [this, sub_self]

theorem separatingLeft_range (hB : B.IsSymm) (hBl : B.SeparatingLeft) (hE : IsSelfAdj B E)
    (hidem : E * E = E) :
    (B.domRestrict₁₂ (LinearMap.range E) (LinearMap.range E)).SeparatingLeft := by
  intro x hx
  have hx' : ∀ w : V, B (x : V) w = 0 := by
    intro w
    have h1 : B (x : V) (E w) = 0 := hx ⟨E w, ⟨w, rfl⟩⟩
    have h2 : B (x : V) (w - E w) = 0 :=
      (orth_range_ker hB hE x.2 (sub_apply_mem_ker hidem w)).1
    have : w = E w + (w - E w) := by abel
    rw [this, map_add, h1, h2, add_zero]
  exact Subtype.ext (hBl (x : V) hx')

theorem apply_eq_of_mem_range (hidem : E * E = E) {v : V} (hv : v ∈ LinearMap.range E) :
    E v = v := by
  obtain ⟨u, rfl⟩ := hv
  have := congrArg (fun f : Module.End K V => f u) hidem
  simpa using this

end Idempotent

end CFSG.RankThree.PartOne.KCUnitaryPlane

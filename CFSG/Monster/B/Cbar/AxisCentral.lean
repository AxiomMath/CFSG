module

public import CFSG.Monster.B.Cbar.TraceTransport
public import CFSG.Monster.B.Short.AxisOrbit

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Parity CFSG.Monster.Generated
  CFSG.Monster.B.Short

theorem gmul_apply_AutO {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO) (a u : SpaceB) :
    gmul (g a) u = g (gmul a (g.symm u)) := by
  have h := (mem_AutO.1 hg).1 a (g.symm u)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem tAxis_AutO {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO) (a u : SpaceB) :
    tAxis (g a) u = g (tAxis a (g.symm u)) := by
  rw [tAxis_apply, tAxis_apply]
  simp only [gmul_apply_AutO hg, map_sub, map_smul, LinearEquiv.symm_apply_apply,
    LinearEquiv.apply_symm_apply]

theorem tAxis_axis {r : Q} (hr : IsShortCoord (coordOf r)) :
    tAxis (axis r) = (rhoEquiv r : SpaceB →ₗ[ℚ] SpaceB) := by
  apply LinearMap.ext
  intro u
  change tAxis (axis r) u = rhoEquiv r u
  rw [tAxis_apply, rhoEquiv_eq_axisPoly hr, axisCubic_apply]
  congr 2
  simp only [map_sub, map_smul]
  module

theorem trace_conj_comp_gmul {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO)
    (T : Module.End ℚ SpaceB) (v : SpaceB) :
    LinearMap.trace ℚ SpaceB (((g : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ T ∘ₗ (g.symm : SpaceB →ₗ[ℚ] SpaceB)) ∘ₗ
      gmul v) = LinearMap.trace ℚ SpaceB (T ∘ₗ gmul (g.symm v)) := by
  have hconj : ((g : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ T ∘ₗ (g.symm : SpaceB →ₗ[ℚ] SpaceB)) ∘ₗ gmul v =
      (g : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ (T ∘ₗ gmul (g.symm v)) ∘ₗ (g.symm : SpaceB →ₗ[ℚ] SpaceB) := by
    apply LinearMap.ext
    intro u
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    congr 2
    have h := (mem_AutO.1 (inv_mem hg)).1 v u
    exact h
  rw [hconj, ← LinearMap.comp_assoc, LinearMap.trace_comp_comm', ← LinearMap.comp_assoc]
  have h1 : (g.symm : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ (g : SpaceB →ₗ[ℚ] SpaceB) = LinearMap.id := by
    apply LinearMap.ext
    intro u
    exact g.symm_apply_apply u
  rw [h1, LinearMap.id_comp]

theorem tAxis_aStar : tAxis aStar = (tStar : SpaceB →ₗ[ℚ] SpaceB) := tAxis_axis isShortCoord_rStar

theorem tAxis_apply_aStar {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO) :
    tAxis (g aStar) =
      (g : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ (tStar : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ (g.symm : SpaceB →ₗ[ℚ] SpaceB) := by
  apply LinearMap.ext
  intro u
  rw [tAxis_AutO hg, tAxis_aStar]
  rfl

theorem trace_tAxis_of_mem {a : SpaceB} (ha : a ∈ axisOrbit) (v : SpaceB) :
    LinearMap.trace ℚ SpaceB (tAxis a ∘ₗ gmul v) =
      bform ((1070 : ℚ) • inA oneA - (4096 : ℚ) • a) v := by
  obtain ⟨g, hg, rfl⟩ := ha
  have hgA : g ∈ AutO := Gmat_le_AutO hg
  rw [tAxis_apply_aStar hgA, trace_conj_comp_gmul hgA]
  have h := trace_rhoL_rStar (g.symm v)
  rw [rhoL] at h
  change LinearMap.trace ℚ SpaceB ((tStar : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ gmul (g.symm v)) = _
  rw [show tStar = rhoEquiv (rMinus 0 1) from rfl, h, ← (mem_AutO.1 hgA).2,
    LinearEquiv.apply_symm_apply, traceVec, map_sub, map_smul, map_smul,
    AutO_apply_inA_oneA hgA]
  rfl

theorem tAxis_injOn : Set.InjOn tAxis axisOrbit := by
  intro a ha b hb hab
  have h : ∀ v, bform (a - b) v = 0 := by
    intro v
    have h1 := trace_tAxis_of_mem ha v
    have h2 := trace_tAxis_of_mem hb v
    rw [hab] at h1
    rw [h1] at h2
    have : bform ((4096 : ℚ) • (a - b)) v = 0 := by
      have e : (4096 : ℚ) • (a - b) =
          ((1070 : ℚ) • inA oneA - (4096 : ℚ) • b) - ((1070 : ℚ) • inA oneA - (4096 : ℚ) • a) := by
        module
      rw [e, map_sub, LinearMap.sub_apply, h2, sub_self]
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_left (by norm_num)
  by_contra hne
  have hpos := bform_self_pos (sub_ne_zero.2 hne)
  rw [h] at hpos
  exact lt_irrefl _ hpos

theorem tAxis_bijOn :
    Set.BijOn tAxis axisOrbit ((fun t : SpaceB ≃ₗ[ℚ] SpaceB => (t : SpaceB →ₗ[ℚ] SpaceB)) ''
      shortClass) := by
  refine ⟨?_, tAxis_injOn, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨g * tStar * g⁻¹, ⟨g, hg, rfl⟩, ?_⟩
    rw [tAxis_apply_aStar (Gmat_le_AutO hg)]
    rfl
  · rintro _ ⟨t, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨g aStar, ⟨g, hg, rfl⟩, ?_⟩
    rw [tAxis_apply_aStar (Gmat_le_AutO hg)]
    rfl

theorem apply_mem_axisOrbit {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gmat) {a : SpaceB}
    (ha : a ∈ axisOrbit) : g a ∈ axisOrbit := by
  obtain ⟨k, hk, rfl⟩ := ha
  exact ⟨g * k, mul_mem hg hk, rfl⟩

theorem commute_tAxis_iff {a : SpaceB} (ha : a ∈ axisOrbit) {g : SpaceB ≃ₗ[ℚ] SpaceB}
    (hg : g ∈ Gmat) :
    (g : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ tAxis a = tAxis a ∘ₗ (g : SpaceB →ₗ[ℚ] SpaceB) ↔ g a = a := by
  have hgA : g ∈ AutO := Gmat_le_AutO hg
  have hconj : tAxis (g a) =
      (g : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ tAxis a ∘ₗ (g.symm : SpaceB →ₗ[ℚ] SpaceB) :=
    LinearMap.ext fun u => tAxis_AutO hgA a u
  constructor
  · intro hc
    apply tAxis_injOn (apply_mem_axisOrbit hg ha) ha
    rw [hconj, ← LinearMap.comp_assoc, hc, LinearMap.comp_assoc]
    have h1 : (g : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ (g.symm : SpaceB →ₗ[ℚ] SpaceB) = LinearMap.id := by
      apply LinearMap.ext
      intro u
      exact g.apply_symm_apply u
    rw [h1, LinearMap.comp_id]
  · intro hfix
    rw [hfix] at hconj
    apply LinearMap.ext
    intro u
    have := LinearMap.congr_fun hconj (g u)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this
    exact this.symm

theorem commute_iff_of_eq_tAxis {a : SpaceB} (ha : a ∈ axisOrbit) {t : SpaceB ≃ₗ[ℚ] SpaceB}
    (ht : (t : SpaceB →ₗ[ℚ] SpaceB) = tAxis a) {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gmat) :
    g * t = t * g ↔ g a = a := by
  rw [← commute_tAxis_iff ha hg, ← ht]
  constructor
  · intro h
    exact LinearMap.ext fun u => LinearEquiv.congr_fun h u
  · intro h
    exact LinearEquiv.ext fun u => LinearMap.congr_fun h u

end CFSG.Monster.B

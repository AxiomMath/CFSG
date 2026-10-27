module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClPoint

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
  {F : LinearMap.BilinForm K V}

theorem no_elations_of_isom [Finite K] [FiniteDimensional K V] (hnd : F.Nondegenerate)
    (halt : F.IsAlt) (hdim : 3 ≤ Module.finrank K V) {b : V} (hb : b ≠ 0)
    (X : Set (V ≃ₗ[K] V)) (hX : ∀ g ∈ X, IsIsom F g)
    (hel : ∀ φ : Module.Dual K V, φ b = 0 → ∃ g ∈ X, ∀ y, g y = y + φ y • b) : False := by
  obtain ⟨u, hub, hu⟩ := exists_perp_not_mem_span (F := F) hdim hb
  obtain ⟨g, hgX, hg⟩ := hel (F u) hub
  have hiso := hX g hgX
  have hE : ∀ y y' : V, F u y' * F y b + F u y * F y' b = 0 := by
    intro y y'
    have h1 := hiso y y'
    rw [hg y, hg y'] at h1
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      form_self halt, mul_zero, add_zero] at h1
    rw [form_comm halt b y'] at h1
    linear_combination h1
  obtain ⟨z, hz⟩ : ∃ z, F z b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hb (hnd.2 b hcon)
  set y' : V := (F z b)⁻¹ • z with hy'
  have hy'b : F y' b = 1 := by
    rw [hy', map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hz]
  have hkey : ∀ y, F u y = F u y' * F y b := by
    intro y
    have := hE y y'
    rw [hy'b] at this
    linear_combination this - (F u y' * F y b) * (two_eq_zero_K (K := K))
  have h0 : u - (F u y') • b = 0 := by
    apply hnd.1
    intro y
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hkey y, form_comm halt b y]
    ring
  exact hu (F u y') (sub_eq_zero.mp h0)

theorem pointRad_smul {e : V} {c : K} (hc : c ≠ 0) :
    pointRadSubgroup F (c • e) = pointRadSubgroup F e := by
  ext g
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, fun v hv => ?_⟩
    · rw [map_smul] at h2
      exact smul_right_injective V hc h2
    · obtain ⟨d, hd⟩ := h3 v (by rw [map_smul, smul_eq_mul, hv, mul_zero])
      refine ⟨d * c, ?_⟩
      rw [hd, smul_smul]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, by rw [map_smul, h2], fun v hv => ?_⟩
    have hv' : F v e = 0 := by
      rw [map_smul, smul_eq_mul] at hv
      exact (mul_eq_zero.mp hv).resolve_left hc
    obtain ⟨d, hd⟩ := h3 v hv'
    refine ⟨d * c⁻¹, ?_⟩
    rw [hd, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]

theorem elationFull_smul {D : Set (V ≃ₗ[K] V)} {e : V} {c : K} (hc : c ≠ 0) :
    ElationFull F D (c • e) ↔ ElationFull F D e := by
  have hF : ∀ v, F v (c • e) = 0 ↔ F v e = 0 := fun v => by
    rw [map_smul, smul_eq_mul]
    exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hc, fun h => by rw [h, mul_zero]⟩
  constructor
  · intro h φ hφ
    obtain ⟨g, hgD, hg⟩ := h (c⁻¹ • φ) (by
      rw [LinearMap.smul_apply, map_smul, hφ, smul_zero, smul_zero])
    refine ⟨g, hgD, fun v hv => ?_⟩
    have hcc : c⁻¹ * φ v * c = φ v := by field_simp
    rw [hg v ((hF v).mpr hv), LinearMap.smul_apply, smul_eq_mul, smul_smul, hcc]
  · intro h φ hφ
    have hφe : φ e = 0 := by
      have : φ (c • e) = c * φ e := by rw [map_smul, smul_eq_mul]
      rw [this] at hφ
      exact (mul_eq_zero.mp hφ).resolve_left hc
    obtain ⟨g, hgD, hg⟩ := h (c • φ) (by
      rw [LinearMap.smul_apply, hφe, smul_zero])
    refine ⟨g, hgD, fun v hv => ?_⟩
    rw [hg v ((hF v).mp hv), LinearMap.smul_apply, smul_eq_mul, smul_smul, mul_comm]

end CFSG.RankThree.GF2n.Stroth80.Classify

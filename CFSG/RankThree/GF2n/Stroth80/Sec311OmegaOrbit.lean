module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClQuad

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exists_apply_eq_of_elationFull_orth {F : LinearMap.BilinForm K V} (hnd : F.Nondegenerate)
    (halt : F.IsAlt) {Qf : QuadraticForm K V} (hQF : Qf.polarBilin = F)
    {H : Subgroup (V ≃ₗ[K] V)} (hH : H ≤ orthSubgroup Qf) {e : V} (he : Qf e = 0)
    (hful : ElationFull F ((H : Set (V ≃ₗ[K] V)) ∩ pointRad F e) e) {e' v : V}
    (he' : Qf e' = 0) (hv : Qf v = 0) (hne : F e' e ≠ 0) (hFv : F v e = F e' e) :
    ∃ g ∈ H, g e' = v := by
  obtain ⟨w, hw⟩ : ∃ w : V, w = v - e' := ⟨_, rfl⟩
  have hwe : F w e = 0 := by
    rw [hw, map_sub, LinearMap.sub_apply, hFv, sub_self]
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K V, ∀ x : V, φ x = (F e' e)⁻¹ * F w x :=
    ⟨(F e' e)⁻¹ • F w, fun x => rfl⟩
  have hφe : φ e = 0 := by
    rw [hφ e, hwe, mul_zero]
  obtain ⟨g, hgD, hg⟩ := hful φ hφe
  have hgH : g ∈ H := hgD.1
  have hgp : g ∈ pointRadSubgroup F e := hgD.2
  obtain ⟨hiso0, hge, -⟩ := hgp
  have hiso : ∀ x y : V, F (g x) (g y) = F x y := hiso0
  have hQg : ∀ x : V, Qf (g x) = Qf x := hH hgH
  have hgeF : F (g e') e = F e' e := by
    have h := hiso e' e
    rw [hge] at h
    exact h
  have hkey : ∀ u : V, F u e = 0 → F (g e' - v) u = 0 := by
    intro u hu
    have h1 : F (g e') (g u) = F e' u := hiso e' u
    rw [hg u hu] at h1
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hgeF] at h1
    have hφu := hφ u
    have hW : F w u = F v u - F e' u := by
      rw [hw, map_sub, LinearMap.sub_apply]
    have hinv : F e' e * (F e' e)⁻¹ = 1 := mul_inv_cancel₀ hne
    rw [map_sub, LinearMap.sub_apply]
    linear_combination h1 - (F e' e) * hφu - (F w u) * hinv - hW
      + (F e' u - F v u) * (two_eq_zero_K (K := K))
  obtain ⟨d, hd⟩ := perp_perp hnd halt e (g e' - v) hkey
  have hge' : g e' = v + d • e := by
    rw [← hd]
    abel
  have hd0 : d = 0 := by
    have h1 : Qf (g e') = d * F e' e := by
      rw [hge', qf_add hQF, qf_smul, he, hv, map_smul, smul_eq_mul, hFv]
      ring
    have h2 : d * F e' e = 0 := by
      rw [← h1, hQg e', he']
    exact (mul_eq_zero.mp h2).resolve_right hne
  exact ⟨g, hgH, by rw [hge', hd0, zero_smul, add_zero]⟩

end CFSG.RankThree.GF2n.Stroth80.Classify

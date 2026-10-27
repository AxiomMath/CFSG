module

public import CFSG.RankThree.GF2n.Smith81.S81VCoreAt
public import CFSG.RankThree.GF2n.Smith81.S81VTransport

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81 CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {G : Type} [Group G] {M Q Z B : Subgroup G} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}

theorem point_clauseU (hσ : IsUnitaryInvolution σ) (e' : K ≃+* Fσ σ) (ψ : M₀.E ≃ₗ[K] E3UWspace σ e')
    (T : Lgen M (LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E)) (A : SUid σ 6 →* (M₀.E ≃ₗ[K] M₀.E))
    (hψA : ∀ g v, ψ (A g v) = e3uWact σ e' g (ψ v))
    {WB : Submodule F (Fin 6 → F)} {gB : SUid σ 6} (hgB : ∀ v, v ∈ WB ↔ ∃ w ∈ W₀ F, gB • w = v)
    (hψB : (fixAt σ A WB).map (ψ : M₀.E →ₗ[K] E3UWspace σ e') =
      Submodule.span K {e3uWact σ e' gB (e3uP0 σ e')})
    {A' : Subgroup G} {W' : Submodule F (Fin 6 → F)} (hti : IsTotIso σ W') (h3 : finrank F W' = 3)
    (hFix : ∀ v, v ∈ fixAt σ A W' ↔ ∃ x ∈ A', M₀.π x = v)
    (hU : ∀ u ∈ PtStab σ W', ∃ t : Lgen M (LB M Q B), (t : G) ∈ QB A' ∧ ∀ v, T t v = A u v) :
    ∃ g ∈ e3uGam σ e',
      (fun a : G => ψ (M₀.π a)) '' (A' : Set G) =
          (Submodule.span K {g (e3uP0 σ e')} : Set (E3UWspace σ e')) ∧
        ∀ u ∈ conjSub g (e3uU0 σ e'), ∃ t : Lgen M (LB M Q B), (t : G) ∈ QB A' ∧
          transportU ψ (T t) = u := by
  obtain ⟨g₁, hg₁⟩ := exists_su_smul_W₀ hσ hti h3
  have hhg : g₁ * gB⁻¹ * gB = g₁ := inv_mul_cancel_right g₁ gB
  have hW'' : ∀ v, v ∈ W' ↔ ∃ w ∈ WB, (g₁ * gB⁻¹) • w = v := by
    intro v
    rw [hg₁ v]
    constructor
    · rintro ⟨w₀, hw₀, rfl⟩
      exact ⟨gB • w₀, (hgB _).2 ⟨w₀, hw₀, rfl⟩, by rw [mul_smul, inv_smul_smul]⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨w₀, hw₀, rfl⟩ := (hgB w).1 hw
      exact ⟨w₀, hw₀, by rw [mul_smul, inv_smul_smul]⟩
  have hfm := fixAt_map A (g₁ * gB⁻¹) hW''
  have hcomp : (ψ : M₀.E →ₗ[K] E3UWspace σ e').comp (A (g₁ * gB⁻¹) : M₀.E →ₗ[K] M₀.E) =
      (e3uWact σ e' (g₁ * gB⁻¹) : E3UWspace σ e' →ₗ[K] E3UWspace σ e').comp
        (ψ : M₀.E →ₗ[K] E3UWspace σ e') := by
    apply LinearMap.ext
    intro v
    exact hψA (g₁ * gB⁻¹) v
  have hF : (fixAt σ A W').map (ψ : M₀.E →ₗ[K] E3UWspace σ e') =
      Submodule.span K {e3uWact σ e' g₁ (e3uP0 σ e')} := by
    rw [hfm, ← Submodule.map_comp, hcomp, Submodule.map_comp, hψB, Submodule.map_span,
      Set.image_singleton]
    simp only [LinearEquiv.coe_coe]
    rw [← LinearEquiv.mul_apply, ← map_mul, hhg]
  have hS : (fun a : G => ψ (M₀.π a)) '' (A' : Set G) =
      ((fixAt σ A W').map (ψ : M₀.E →ₗ[K] E3UWspace σ e') : Set (E3UWspace σ e')) := by
    ext w
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe]
      exact Submodule.mem_map.2 ⟨M₀.π a, (hFix (M₀.π a)).2 ⟨a, ha, rfl⟩, rfl⟩
    · intro hw
      rw [SetLike.mem_coe] at hw
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
      obtain ⟨x, hx, hxv⟩ := (hFix v).1 hv
      exact ⟨x, hx, by simp [hxv]⟩
  refine ⟨e3uWact σ e' g₁, MonoidHom.mem_range.2 ⟨g₁, rfl⟩, ?_, ?_⟩
  · rw [hS, hF]
  · intro u hu
    obtain ⟨u₀, hu₀, hgu⟩ := mem_conjSub.1 hu
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 (show u₀ ∈ (e3uU0Sub σ).map (e3uWact σ e') from hu₀)
    rw [e3uU0Sub_eq_ptStab] at hk
    have hk' : g₁ * k * g₁⁻¹ ∈ PtStab σ W' := by
      rw [ptStab_conj g₁ hg₁]
      exact Subgroup.mem_map_of_mem (MulAut.conj g₁).toMonoidHom hk
    obtain ⟨t, htQB, htT⟩ := hU _ hk'
    refine ⟨t, htQB, ?_⟩
    have hTt : T t = A (g₁ * k * g₁⁻¹) := LinearEquiv.ext htT
    rw [hTt, transportU_of_equivariant (e3uWact σ e') A ψ hψA, ← hgu, map_mul, map_mul, map_inv]

end CFSG.RankThree.GF2n.Smith81.S81V


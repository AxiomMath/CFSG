module

public import CFSG.LocalAnalysis.StandardType.GGStdPosTorus
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

private theorem mul_center_mul {K : Type*} [Group K] {z : K} (hz : z ∈ Subgroup.center K)
    (a b c : K) : a * (b * z) * c = a * b * c * z := by
  rw [Subgroup.mem_center_iff] at hz
  calc a * (b * z) * c = a * b * (z * c) := by group
    _ = a * b * (c * z) := by rw [hz c]
    _ = a * b * c * z := by group

theorem ggStdPos_conj_mem_map_iSup {K G : Type*} [Group K] [Group G]
    {D : UniversalRootDatum K} {ψ : K →* G} {s : G}
    (hs : ∀ γ ∈ D.roots, ∃ h ∈ ggTorus D, ∀ z ∈ D.rootGroup γ, s * ψ z * s⁻¹ = ψ (h * z * h⁻¹))
    {A : Set (Fin D.rank → ℤ)} (hA : A ⊆ D.roots) {y : K}
    (hy : y ∈ ⨆ γ ∈ A, D.rootGroup γ) :
    ∃ y' ∈ ⨆ γ ∈ A, D.rootGroup γ, s * ψ y * s⁻¹ = ψ y' := by
  have hle : ⨆ γ ∈ A, D.rootGroup γ ≤
      ((⨆ γ ∈ A, D.rootGroup γ).map ψ).comap ((MulAut.conj s).toMonoidHom.comp ψ) := by
    refine iSup₂_le fun γ hγ z hz => ?_
    obtain ⟨h, hh, hz'⟩ := hs γ (hA hγ)
    have hN := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh γ) (hA hγ)
    refine ⟨h * z * h⁻¹, le_iSup₂_of_le (f := fun γ (_ : γ ∈ A) => D.rootGroup γ) γ hγ le_rfl
      ((Subgroup.mem_normalizer_iff.mp hN z).mp hz), ?_⟩
    rw [← hz' z hz]
    rfl
  obtain ⟨y', hy', he⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp (hle hy))
  exact ⟨y', hy', he.symm⟩

theorem ggStdPos_exists_conj_eq {K G : Type*} [Group K] [Group G] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) {ψ : K →* G}
    (hker : ψ.ker ≤ Subgroup.center K) {s : G}
    (hs : ∀ γ ∈ D.roots, ∃ h ∈ ggTorus D, ∀ z ∈ D.rootGroup γ, s * ψ z * s⁻¹ = ψ (h * z * h⁻¹))
    {x : K} {w : (coxeterMatrix D.isFiniteType).Group} (hx : ActsAs D x w) :
    ∃ m : K, s * ψ x * s⁻¹ = ψ m ∧ x⁻¹ * m ∈ ⨆ i, H i := by
  have hxK : x ∈ ⨆ γ ∈ D.roots, D.rootGroup γ := by
    rw [hct.iSup_eq_top]
    exact Subgroup.mem_top x
  obtain ⟨m, -, hm⟩ := ggStdPos_conj_mem_map_iSup hs subset_rfl hxK
  refine ⟨m, hm, ggStdPos_mem_iSup_torus hct hext hBU fun γ hγ y hy => ?_⟩
  have hwγ : weylAction D.isFiniteType w γ ∈ D.roots := weylAction_mem_roots _ w hγ
  obtain ⟨h₁, hh₁, he₁⟩ := hs γ hγ
  obtain ⟨h₂, hh₂, he₂⟩ := hs _ hwγ
  have hN₁ := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh₁ γ) hγ
  have hN₂ := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh₂ _) hwγ
  have hy₀ : h₁⁻¹ * y * h₁ ∈ D.rootGroup γ := by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hN₁) y).mp hy
    rwa [inv_inv] at h
  have e₁ : s * ψ (h₁⁻¹ * y * h₁) * s⁻¹ = ψ y := by
    rw [he₁ _ hy₀]
    congr 1
    group
  have hxy := hx.conj_mem hγ hy₀
  have e₂ : ψ (m * y * m⁻¹) = ψ (h₂ * (x * (h₁⁻¹ * y * h₁) * x⁻¹) * h₂⁻¹) := by
    calc ψ (m * y * m⁻¹) = ψ m * ψ y * (ψ m)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = s * ψ x * s⁻¹ * (s * ψ (h₁⁻¹ * y * h₁) * s⁻¹) * (s * ψ x * s⁻¹)⁻¹ := by
          rw [hm, e₁]
      _ = s * ψ (x * (h₁⁻¹ * y * h₁) * x⁻¹) * s⁻¹ := by
          rw [map_mul ψ (x * (h₁⁻¹ * y * h₁)), map_mul ψ x, map_inv]
          group
      _ = _ := he₂ _ hxy
  obtain ⟨z, hz, hmy⟩ : ∃ z ∈ Subgroup.center K,
      m * y * m⁻¹ = h₂ * (x * (h₁⁻¹ * y * h₁) * x⁻¹) * h₂⁻¹ * z :=
    ⟨(h₂ * (x * (h₁⁻¹ * y * h₁) * x⁻¹) * h₂⁻¹)⁻¹ * (m * y * m⁻¹),
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, e₂, inv_mul_cancel]), by group⟩
  refine ⟨x⁻¹ * (h₂ * (x * (h₁⁻¹ * y * h₁) * x⁻¹) * h₂⁻¹) * x, ?_, z, hz, ?_⟩
  · have h := hx.inv_conj_mem hwγ ((Subgroup.mem_normalizer_iff.mp hN₂ _).mp hxy)
    rwa [weylAction_inv_apply_apply] at h
  · calc x⁻¹ * m * y * (x⁻¹ * m)⁻¹ = x⁻¹ * (m * y * m⁻¹) * x := by group
      _ = _ := by rw [hmy, mul_center_mul hz]

end CFSG.StandardType

end

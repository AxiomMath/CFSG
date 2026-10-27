module

public import CFSG.LocalAnalysis.StandardType.GGStdPosTorusFix
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

private theorem conj_psi_mem_of_actsAs {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {F : Type*} [Field F] [CharP F 2]
    {x : (Fin D.rank → ℤ) → F → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (hE : ChevalleyExtras D F x C O)
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {p : ℕ}
    {Bs : Subgroup G} (hBs : GGKGPosStdPos D ψ Bs)
    (hN : Bs ≤ Subgroup.normalizer (ψ.range : Set G)) (hpow : ∀ b ∈ Bs, b ^ p = 1)
    (hC3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) {k : K}
    {w : (coxeterMatrix D.isFiniteType).Group} (hk : ActsAs D k w) {b : G} (hb : b ∈ Bs) :
    ψ k * b * (ψ k)⁻¹ ∈ Bs := by
  have hnorm : ∀ h ∈ ggTorus D, ∀ γ ∈ D.roots,
      h ∈ Subgroup.normalizer (D.rootGroup γ : Set K) := fun h hh γ hγ =>
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh γ) hγ
  obtain ⟨m, hm⟩ : ψ k * b * (ψ k)⁻¹ * b⁻¹ ∈ ψ.range := by
    have h1 : b * (ψ k)⁻¹ * b⁻¹ ∈ ψ.range :=
      (Subgroup.mem_normalizer_iff.mp (hN hb) _).mp (inv_mem ⟨k, rfl⟩)
    have e : ψ k * b * (ψ k)⁻¹ * b⁻¹ = ψ k * (b * (ψ k)⁻¹ * b⁻¹) := by group
    rw [e]
    exact mul_mem ⟨k, rfl⟩ h1
  have hmT : m ∈ ggTorus D := by
    rw [ggStdPos_ggTorus_eq hct hext hBU]
    refine ggStdPos_mem_iSup_torus hct hext hBU fun γ hγ y hy => ?_
    obtain ⟨h₁, hh₁, hz₁⟩ := hBs b hb γ hγ
    obtain ⟨h₂, hh₂, hz₂⟩ := hBs b hb _ (weylAction_mem_roots _ w⁻¹ hγ)
    have hy₁ : h₁⁻¹ * y * h₁ ∈ D.rootGroup γ := by
      have h0 := (Subgroup.mem_normalizer_iff.mp (hnorm _ (inv_mem hh₁) γ hγ) y).mp hy
      rwa [inv_inv] at h0
    have hb₁ : b⁻¹ * ψ y * b = ψ (h₁⁻¹ * y * h₁) := by
      have h0 := hz₁ _ hy₁
      rw [show h₁ * (h₁⁻¹ * y * h₁) * h₁⁻¹ = y by group] at h0
      rw [← h0]
      group
    have hb₂ := hz₂ _ (hk.inv_conj_mem hγ hy₁)
    have hm' : k * h₂ * k⁻¹ * h₁⁻¹ ∈ ggTorus D :=
      mul_mem (ggStdPos_conj_mem_ggTorus_of_actsAs hh₂ hk) (inv_mem hh₁)
    have key : ψ (m * y * m⁻¹) =
        ψ ((k * h₂ * k⁻¹ * h₁⁻¹) * y * (k * h₂ * k⁻¹ * h₁⁻¹)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hm]
      calc ψ k * b * (ψ k)⁻¹ * b⁻¹ * ψ y * (ψ k * b * (ψ k)⁻¹ * b⁻¹)⁻¹
          = ψ k * (b * ((ψ k)⁻¹ * (b⁻¹ * ψ y * b) * ψ k) * b⁻¹) * (ψ k)⁻¹ := by group
        _ = ψ k * (b * ψ (k⁻¹ * (h₁⁻¹ * y * h₁) * k) * b⁻¹) * (ψ k)⁻¹ := by
          rw [hb₁]
          simp only [map_mul, map_inv]
        _ = ψ (k * (h₂ * (k⁻¹ * (h₁⁻¹ * y * h₁) * k) * h₂⁻¹) * k⁻¹) := by
          rw [hb₂]
          simp only [map_mul, map_inv]
        _ = ψ ((k * h₂ * k⁻¹ * h₁⁻¹) * y * (k * h₂ * k⁻¹ * h₁⁻¹)⁻¹) := by
          congr 1
          group
    refine ⟨(k * h₂ * k⁻¹ * h₁⁻¹) * y * (k * h₂ * k⁻¹ * h₁⁻¹)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hnorm _ hm' γ hγ) y).mp hy,
      ((k * h₂ * k⁻¹ * h₁⁻¹) * y * (k * h₂ * k⁻¹ * h₁⁻¹)⁻¹)⁻¹ * (m * y * m⁻¹), hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, key, inv_mul_cancel]
  have hcm := ggStdPos_psi_mem_centralizer hct hext hBU hE ψ hker hBs m hmT
  have hcomm : Commute (ψ m) b := (Subgroup.mem_centralizer_iff.mp hcm b hb).symm
  have he : ψ k * b * (ψ k)⁻¹ = ψ m * b := by
    rw [hm]
    group
  have hcp : ψ m ^ p = 1 := by
    have h1 : (ψ k * b * (ψ k)⁻¹) ^ p = 1 := by rw [conj_pow, hpow b hb, mul_one, mul_inv_cancel]
    rwa [he, hcomm.mul_pow, hpow b hb, mul_one] at h1
  rw [he]
  exact mul_mem (hC3 _ hcm hcp) hb

theorem ggStdPos_psi_mem_normalizer {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {F : Type*} [Field F] [CharP F 2]
    {x : (Fin D.rank → ℤ) → F → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (hE : ChevalleyExtras D F x C O)
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {p : ℕ}
    {Bs : Subgroup G} (hBs : GGKGPosStdPos D ψ Bs)
    (hN : Bs ≤ Subgroup.normalizer (ψ.range : Set G)) (hpow : ∀ b ∈ Bs, b ^ p = 1)
    (hC3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) {k : K}
    {w : (coxeterMatrix D.isFiniteType).Group} (hk : ActsAs D k w) :
    ψ k ∈ Subgroup.normalizer (Bs : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun b => ⟨fun hb =>
    conj_psi_mem_of_actsAs hct hext hBU hE ψ hker hBs hN hpow hC3 hk hb, fun hb => ?_⟩
  have h1 := conj_psi_mem_of_actsAs hct hext hBU hE ψ hker hBs hN hpow hC3 hk.inv hb
  rw [map_inv, inv_inv, show (ψ k)⁻¹ * (ψ k * b * (ψ k)⁻¹) * ψ k = b by group] at h1
  exact h1

end CFSG.StandardType

end

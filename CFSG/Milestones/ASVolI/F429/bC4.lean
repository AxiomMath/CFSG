module

public import CFSG.Milestones.ASVolI.F429.Gen
public import CFSG.Milestones.ASVolI.F429.bC7
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsG2

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.H13.Sec53F.BA

section Generic

theorem burnsideF429b_inner_of_borelAutData {Y : Type} [Group Y] {U H : Subgroup Y}
    {F : Subgroup (MulAut Y)} (D : BorelAutData U H F) (β : MulAut Y)
    (h1 : ∀ x, β x ∈ U ↔ x ∈ U) (h2 : ∀ h ∈ H, β h * h⁻¹ ∈ U) :
    β ∈ (MulAut.conj : Y →* MulAut Y).range := by
  obtain ⟨g, hg, τ, hτ, rfl⟩ := D.normal_form β h1
  obtain ⟨u₀, hu₀, h₀, hh₀, rfl⟩ := D.B_eq g hg
  have hfix : ∀ h ∈ H, τ h = h := by
    intro h hh
    have hτh : τ h ∈ H := D.F_H τ hτ h hh
    have hc := h2 h hh
    rw [MulAut.mul_apply, MulAut.conj_apply] at hc
    have hcomm : h₀ * τ h = τ h * h₀ := D.H_comm h₀ hh₀ (τ h) hτh
    have e1 : u₀ * h₀ * τ h * (u₀ * h₀)⁻¹ * h⁻¹ = u₀ * τ h * u₀⁻¹ * h⁻¹ := by
      calc u₀ * h₀ * τ h * (u₀ * h₀)⁻¹ * h⁻¹ = u₀ * (h₀ * τ h) * h₀⁻¹ * u₀⁻¹ * h⁻¹ := by group
        _ = u₀ * (τ h * h₀) * h₀⁻¹ * u₀⁻¹ * h⁻¹ := by rw [hcomm]
        _ = u₀ * τ h * u₀⁻¹ * h⁻¹ := by group
    rw [e1] at hc
    have hu1 : h * u₀ * h⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (D.H_le hh) u₀).1 hu₀
    have hmem : τ h * h⁻¹ ∈ U := by
      have e2 : τ h * h⁻¹ = u₀⁻¹ * (u₀ * τ h * u₀⁻¹ * h⁻¹) * (h * u₀ * h⁻¹) := by group
      rw [e2]
      exact U.mul_mem (U.mul_mem (U.inv_mem hu₀) hc) hu1
    exact mul_inv_eq_one.1 (D.U_inf_H _ hmem (H.mul_mem hτh (H.inv_mem hh)))
  rw [D.F_faithful τ hτ hfix, mul_one]
  exact ⟨u₀ * h₀, rfl⟩

theorem burnsideF429b_key4_of_borelAutData {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    [Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥) {C : Type} [Group C]
    (Ψ : C ≃* ↥Gp) {B U H : Subgroup C} {F : Subgroup (MulAut C)} (D : BorelAutData U H F)
    (hB : (M₁ ⊓ M₂).subgroupOf Gp = B.map Ψ.toMonoidHom) (hU : pCoreOf 2 B = U) (hH : H ≤ B) :
    ∀ r ∈ M₁ ⊓ M₂,
      (∀ b ∈ Gp ⊓ (M₁ ⊓ M₂), r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  intro r hr hcomm
  set φ : C →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
  have hφx : ∀ x : C, φ x = ((Ψ x : ↥Gp) : E) := fun x => rfl
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = B.map φ := burnsideF429_inf_eq_map Ψ hB
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = U.map φ := by
    rw [hGB, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ hφ, hU]
  have hrN := burnsideF429_le_normalizer_pCore_inf (Gp := Gp) (M₁ ⊓ M₂) hr
  let β : MulAut C := (Ψ.trans (burnsideF4d_rho Gp r)).trans Ψ.symm
  have hβφ : ∀ x : C, φ (β x) = r * φ x * r⁻¹ := by
    intro x
    show ((Ψ (Ψ.symm (burnsideF4d_rho Gp r (Ψ x))) : ↥Gp) : E) = r * ((Ψ x : ↥Gp) : E) * r⁻¹
    rw [MulEquiv.apply_symm_apply]
    exact burnsideF4d_rho_apply r (Ψ x)
  have hmemU : ∀ x : C, x ∈ U ↔ φ x ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
    intro x
    rw [hS]
    exact (Subgroup.mem_map_iff_mem hφ).symm
  have h1 : ∀ x, β x ∈ U ↔ x ∈ U := by
    intro x
    rw [hmemU, hmemU, hβφ]
    exact ((Subgroup.mem_normalizer_iff.1 hrN) (φ x)).symm
  have h2 : ∀ h ∈ H, β h * h⁻¹ ∈ U := by
    intro h hh
    rw [hmemU, map_mul, map_inv, hβφ]
    have hb : φ h ∈ Gp ⊓ (M₁ ⊓ M₂) := by
      rw [hGB]
      exact ⟨h, hH hh, rfl⟩
    exact hcomm (φ h) hb
  obtain ⟨g, hg⟩ := burnsideF429b_inner_of_borelAutData D β h1 h2
  have hρ : burnsideF4d_rho Gp r = burnsideF4d_rho Gp ((Ψ g : ↥Gp) : E) := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    obtain ⟨x, rfl⟩ := Ψ.surjective y
    rw [burnsideF4d_rho_apply, burnsideF4d_rho_apply]
    have e1 := hβφ x
    rw [← hg, MulAut.conj_apply, map_mul, map_mul, map_inv] at e1
    rw [← hφx, ← hφx, ← e1]
  have hr' := burnsideF4d_rho_injective hc hρ
  rw [hr']
  exact (Ψ g).2

end Generic

section G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem burnsideF429b_key4_G2 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ Gp ⊓ (M₁ ⊓ M₂), r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  intro r hr _ _ hcomm
  haveI := hyp.normal
  obtain ⟨K, fK, finK, cK, hcard, Ψ, -, hB⟩ := burnsideF429b_G2_chartB hyp.toHypF_4_4g
  have hH : torusSub Tag.G2 K ≤ borelSub Tag.G2 K :=
    le_sup_right.trans (posUnipotentSub_sup_torusSub (τ := Tag.G2) (K := K)).le
  exact burnsideF429b_key4_of_borelAutData hyp.centralizer_trivial Ψ
    (CFSG.Quasithin.H13.Sec53F.G2.borelAutData_g2 hf hcard) hB burnsideF429b_G2_pCoreOf_borel
    hH r hr hcomm

end G2

section D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Quasithin.H13.F431.D4q.Struct

theorem burnsideF429b_D4_pCore_B {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) :
    pCoreOf 2 (Pst0 σ ⊓ Pst1 σ) = Ust σ := by
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hB : Pst0 σ ⊓ Pst1 σ = Subgroup.normalizer (Ust σ : Set (Cm σ)) := by
    rw [CFSG.Quasithin.H13.F431.D4q.Hex.d4_normalizer_eq σ,
      ← CFSG.Quasithin.H13.Sec53F.TriD4.P0_inf_P1 σ]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  rw [hB]
  exact burnsideF4gD4Inv_pCoreOf_normalizer
    (CFSG.Quasithin.H13.F431.D4q.Hex.d4_yamStd σ hf hK hσq).sylow

theorem burnsideF429b_key4_D4tw {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ Gp ⊓ (M₁ ⊓ M₂), r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  intro r hr _ _ hcomm
  haveI := hyp.normal
  obtain ⟨K, fK, finK, cK, σ, hσ3, hf1, hK, hσq, Ψ, h1, h2⟩ :=
    burnsideF429b_D4_chart hyp.toHypF_4_4g
  have hH : (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤ Pst0 σ ⊓ Pst1 σ := by
    intro x hx
    have hxB : (x : ModGL TwistTag.D4.tag K) ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom :=
      graphFixedRootTorus_le_graphFixedRootBorel (Subgroup.mem_subgroupOf.1 hx)
    exact ⟨Subgroup.mem_subgroupOf.2 (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _ hxB),
      Subgroup.mem_subgroupOf.2 (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _ hxB)⟩
  exact burnsideF429b_key4_of_borelAutData hyp.centralizer_trivial Ψ
    (CFSG.Quasithin.H13.Sec53F.TriD4.borelAutData_d4 σ hf1 hK hσq)
    (burnsideF429b_inf_subgroupOf Ψ h1 h2) (burnsideF429b_D4_pCore_B σ hf1 hK hσq) hH r hr hcomm

end D4

end CFSG.ASVolI

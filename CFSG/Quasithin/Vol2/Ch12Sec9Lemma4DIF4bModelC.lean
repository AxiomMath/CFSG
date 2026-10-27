module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bModelO2

public section

namespace CFSG.Quasithin.H13.C1294.Model

open CFSG.Quasithin CFSG.Open

theorem stabM_inf_Omega {Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)} (hΩG : Ω ≤ GM)
    (hrel : Ω.relIndex GM = 2) : stabM Sm ⊓ Ω = HM := by
  ext γ
  constructor
  · intro h
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 h).1, hΩG (Subgroup.mem_inf.1 h).2⟩
  · intro h
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 h).1,
      stab_le_Omega hΩG hrel (Subgroup.mem_inf.1 h).2 (Subgroup.mem_inf.1 h).1⟩

theorem card_Omega {Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)} (hΩG : Ω ≤ GM)
    (hrel : Ω.relIndex GM = 2) (hGM : Nat.card GM = 40320) : Nat.card Ω = 20160 := by
  have h := Subgroup.relIndex_mul_card Ω GM
  rw [hrel, inf_eq_left.2 hΩG, hGM] at h
  omega

theorem model_claims {Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)} (hΩG : Ω ≤ GM)
    (hrel : Ω.relIndex GM = 2) (hGM : Nat.card GM = 40320) :
    (∀ γ ∈ GM, (∀ v, v ∈ Sm ↔ γ v ∈ Sm) → γ ∈ Ω) ∧
    (stabM Sm).relIndex Ω = 15 ∧
    Nat.card (pCoreOf 2 (stabM Sm ⊓ Ω)) = 8 ∧
    ∀ γ ∈ stabM Sm ⊓ Ω, (∀ s ∈ Sm, γ s = s) ↔ γ ∈ pCoreOf 2 (stabM Sm ⊓ Ω) := by
  have hHΩ := stabM_inf_Omega hΩG hrel
  refine ⟨fun γ hγ hS => stab_le_Omega hΩG hrel hγ hS, ?_, ?_, ?_⟩
  ·
    have h := Subgroup.relIndex_mul_card (stabM Sm) Ω
    rw [hHΩ, card_Omega hΩG hrel hGM] at h
    have hH : Nat.card ↥HM = 1344 := card_stab
    rw [hH] at h
    omega
  · rw [hHΩ]
    rw [CFSG.Open.pCoreOf, ← Nat.card_congr ((CFSG.pCore 2 ↥HM).equivMapOfInjective HM.subtype
      HM.subtype_injective).toEquiv, pCore_HM, card_K0_subgroupOf]
  · intro γ hγ
    rw [hHΩ] at hγ ⊢
    constructor
    · intro hfix
      rw [CFSG.Open.pCoreOf, Subgroup.mem_map]
      refine ⟨⟨γ, hγ⟩, ?_, rfl⟩
      rw [pCore_HM, Subgroup.mem_subgroupOf]
      exact ⟨(Subgroup.mem_inf.1 hγ).2, fun v hv => hfix v hv⟩
    · intro hmem
      rw [CFSG.Open.pCoreOf, Subgroup.mem_map] at hmem
      obtain ⟨x, hx, hxγ⟩ := hmem
      rw [pCore_HM, Subgroup.mem_subgroupOf] at hx
      have : (x : VM ≃ₗ[ZMod 2] VM) = γ := hxγ
      intro s hs
      rw [← this]
      exact hx.2 s hs

end CFSG.Quasithin.H13.C1294.Model

end

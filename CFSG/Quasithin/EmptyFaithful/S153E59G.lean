module

public import CFSG.Quasithin.EmptyFaithful.S153E59F
public import CFSG.Quasithin.EmptyFaithful.S153E59A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E59

section K

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem mem_oTwoUpper_mul_iff (cx : Ctx15350 T Mc M V₁ V₂ t) {x : G} (hx : x ∈ Mc) :
    rho cx ⟨x, hx⟩ ∈ oTwoUpper (HStar153 T M V₁ Mc) ↔
      ∃ k ∈ oTwoUpper Mc, ∃ q ∈ pCoreOf 2 Mc, x = k * q := by
  constructor
  · intro h
    rw [← map_rho_oTwoUpper cx] at h
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp h
    have hkK : (k : G) ∈ oTwoUpper Mc := Subgroup.mem_subgroupOf.mp hk
    refine ⟨k, hkK, (k : G)⁻¹ * x, ?_, by group⟩
    have : rho cx (k⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, hkx, inv_mul_cancel]
    exact (rho_eq_one_iff cx _).mp this
  · rintro ⟨k, hk, q, hq, rfl⟩
    have hkM : k ∈ Mc := oTwoUpper_le Mc hk
    have hqM : q ∈ Mc := pCoreOf_le 2 Mc hq
    have h1 : rho cx ⟨k * q, hx⟩ = rho cx ⟨k, hkM⟩ := by
      have : (⟨k * q, hx⟩ : ↥Mc) = ⟨k, hkM⟩ * ⟨q, hqM⟩ := rfl
      rw [this, map_mul, (rho_eq_one_iff cx ⟨q, hqM⟩).mpr hq, mul_one]
    rw [h1, ← map_rho_oTwoUpper cx]
    exact Subgroup.mem_map.mpr ⟨⟨k, hkM⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩

theorem not_oTwoUpper_le_pCoreOf (cx : Ctx15350 T Mc M V₁ V₂ t) (hH : HStarFacts cx) :
    ¬ oTwoUpper Mc ≤ pCoreOf 2 Mc := by
  intro h
  have h1 : ((oTwoUpper Mc).subgroupOf Mc).map (rho cx) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_bot]
    exact (rho_eq_one_iff cx k).mpr (h (Subgroup.mem_subgroupOf.mp hk))
  rw [map_rho_oTwoUpper cx] at h1
  have := hH.card_Ks
  rw [h1, Subgroup.card_bot] at this
  omega

theorem U_le_oTwoUpper (cx : Ctx15350 T Mc M V₁ V₂ t) (hH : HStarFacts cx)
    (hirr : ∀ W : Subgroup G, quasithinOmegaOneCenter T ≤ W → W ≤ UH153 T M V₁ Mc →
      Mc ≤ Subgroup.normalizer (W : Set G) → W = quasithinOmegaOneCenter T ∨ W = UH153 T M V₁ Mc)
    (hnab : IsNonabelian153 (UH153 T M V₁ Mc)) : UH153 T M V₁ Mc ≤ oTwoUpper Mc := by
  set U := UH153 T M V₁ Mc with hU
  set Z := quasithinOmegaOneCenter T with hZ
  set K := oTwoUpper Mc with hK
  have hUnorm : Mc ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure _ _
  have hKnorm : Mc ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper Mc
  have hZnorm : Mc ≤ Subgroup.normalizer (Z : Set G) := cx.hF.H_normalizes_V₁
  have hUKnorm : Mc ≤ Subgroup.normalizer ((U ⊓ K : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hUnorm hg, hKnorm hg⟩
  have hZN₀ : Z ≤ (U ⊓ K) ⊔ Z := le_sup_right
  have hN₀U : (U ⊓ K) ⊔ Z ≤ U := sup_le inf_le_left (Z_le_U cx)
  have hnorm : Mc ≤ Subgroup.normalizer (((U ⊓ K) ⊔ Z : Subgroup G) : Set G) :=
    B2F.le_normalizer_sup hUKnorm hZnorm
  rcases hirr _ hZN₀ hN₀U hnorm with hN | hN
  · exfalso
    refine not_oTwoUpper_le_pCoreOf cx hH fun k hk => ?_
    rw [cx.hF.pCoreOf_eq_centralizerMod]
    have hkM : k ∈ Mc := oTwoUpper_le Mc hk
    refine ⟨hkM, cx.hF.H_normalizes_V₁ hkM, fun u hu => ?_⟩
    have h1 : k * u * k⁻¹ * u⁻¹ ∈ U ⊓ K := by
      refine ⟨U.mul_mem (S153E.U_conj_mem hkM hu) (U.inv_mem hu), ?_⟩
      have : k * u * k⁻¹ * u⁻¹ = k * (u * k⁻¹ * u⁻¹) := by group
      rw [this]
      refine K.mul_mem hk ?_
      exact (Subgroup.mem_normalizer_iff.mp (hKnorm (U_le_Mc cx hu)) k⁻¹).mp (K.inv_mem hk)
    have h2 : k * u * k⁻¹ * u⁻¹ ∈ (U ⊓ K) ⊔ Z := (le_sup_left : U ⊓ K ≤ (U ⊓ K) ⊔ Z) h1
    rw [hN] at h2
    exact h2
  ·
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    have hmul : (((U ⊓ K) ⊔ Z : Subgroup G) : Set G) = ((U ⊓ K : Subgroup G) : Set G) * (Z : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right (U ⊓ K) Z
        (fun g hg => hZnorm ((U_le_Mc cx hg.1)))
    have haN : a ∈ (((U ⊓ K) ⊔ Z : Subgroup G) : Set G) := by rw [hN]; exact ha
    have hbN : b ∈ (((U ⊓ K) ⊔ Z : Subgroup G) : Set G) := by rw [hN]; exact hb
    rw [hmul] at haN hbN
    obtain ⟨a₀, ha₀, z₁, hz₁, rfl⟩ := haN
    obtain ⟨b₀, hb₀, z₂, hz₂, rfl⟩ := hbN
    have hz₁M : z₁ ∈ Mc := U_le_Mc cx (Z_le_U cx hz₁)
    have hz₂M : z₂ ∈ Mc := U_le_Mc cx (Z_le_U cx hz₂)
    have ha₀M : a₀ ∈ Mc := U_le_Mc cx ha₀.1
    have hb₀M : b₀ ∈ Mc := U_le_Mc cx hb₀.1
    have h1 : z₁ * (b₀ * z₂) = (b₀ * z₂) * z₁ := by
      have e1 : z₁ * b₀ = b₀ * z₁ := (Z_central cx hb₀M hz₁).symm
      have e2 : z₁ * z₂ = z₂ * z₁ := Z_central cx hz₁M hz₂
      calc z₁ * (b₀ * z₂) = (z₁ * b₀) * z₂ := by group
        _ = (b₀ * z₁) * z₂ := by rw [e1]
        _ = b₀ * (z₁ * z₂) := by group
        _ = b₀ * (z₂ * z₁) := by rw [e2]
        _ = (b₀ * z₂) * z₁ := by group
    have h2 : z₂ * a₀ = a₀ * z₂ := (Z_central cx ha₀M hz₂).symm
    have hcomm : ⁅a₀ * z₁, b₀ * z₂⁆ = ⁅a₀, b₀⁆ := by
      rw [commutator_mul_central_left h1, commutator_mul_central_right h2]
    have hcZ : ⁅a₀ * z₁, b₀ * z₂⁆ ∈ Z := by
      rw [commutatorElement_def]
      exact commutator_U (cx := cx) (hN₀U (by rw [hN]; exact ha)) (hN₀U (by rw [hN]; exact hb))
    have hcne : ⁅a₀ * z₁, b₀ * z₂⁆ ≠ 1 := by
      intro h
      apply hab
      rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
      exact h
    rw [hcomm] at hcZ hcne
    have hc0 : ⁅a₀, b₀⁆ ∈ U ⊓ K := by
      rw [commutatorElement_def]
      exact (U ⊓ K).mul_mem ((U ⊓ K).mul_mem ((U ⊓ K).mul_mem ha₀ hb₀) ((U ⊓ K).inv_mem ha₀))
        ((U ⊓ K).inv_mem hb₀)
    have hZ0 : Z ≤ U ⊓ K := by
      refine le_of_card_eq_two_of_inf_ne_bot (card_Z cx) ?_
      intro hbot
      have : ⁅a₀, b₀⁆ ∈ Z ⊓ (U ⊓ K) := ⟨hcZ, hc0⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hcne this
    intro u hu
    have : u ∈ (U ⊓ K) ⊔ Z := by rw [hN]; exact hu
    have h3 : (U ⊓ K) ⊔ Z = U ⊓ K := sup_eq_left.mpr hZ0
    rw [h3] at this
    exact this.2

end K

end S153E59

end CFSG.Quasithin

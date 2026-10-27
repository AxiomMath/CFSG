module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1Defs
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeToralCentHolds
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.HardMathSupport.Lang.E6Descent CFSG.Open

private theorem ti_mem_inf_conj_iff {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G))
    (w : G) : w ∈ A ⊓ B ↔ g * w * g⁻¹ ∈ A ⊓ B := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨(Subgroup.mem_normalizer_iff.1 hA w).1 ha,
      (Subgroup.mem_normalizer_iff.1 hB w).1 hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨(Subgroup.mem_normalizer_iff.1 hA w).2 ha,
      (Subgroup.mem_normalizer_iff.1 hB w).2 hb⟩

theorem isToralE6_of_inf_twInndiagAut_ne_bot (h82 : GGTwE6ThreeTwoLocalInnToralInput) {f : ℕ}
    (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1) (Ω : Type) [Field Ω]
    [Algebra (GaloisField 2 (2 * f)) Ω] [IsAlgClosure (GaloisField 2 (2 * f)) Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ f)
    (Φ : ↥(TwistedDiag.Rgrp Ω Fr) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    (hΦinj : Function.Injective Φ) (hΦrange : Φ.range = LayerSixE.twInndiagAut f)
    {X U : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))}
    (hXI : X ≤ LayerSixE.twInndiagAut f) (hel : IsElemAbelian 3 X) (hc : Nat.card X = 3 ^ 4)
    (hU2 : IsPGroup 2 U) (hXU : X ≤ Subgroup.normalizer (U : Set _))
    (hUI : U ⊓ LayerSixE.twInndiagAut f ≠ ⊥) :
    IsToralE6 Ω ((X.comap Φ).map (TwistedDiag.Rgrp Ω Fr).subtype) := by
  classical
  let R := TwistedDiag.Rgrp Ω Fr
  let W : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))) := U ⊓ LayerSixE.twInndiagAut f
  let XR : Subgroup (ModGL Tag.E6 Ω) := (X.comap Φ).map R.subtype
  let V : Subgroup (ModGL Tag.E6 Ω) := (W.comap Φ).map R.subtype
  have hWrange : W ≤ Φ.range := by
    rw [hΦrange]
    exact inf_le_right
  have hXR : XR ≤ R := Subgroup.map_subtype_le (X.comap Φ)
  have hVR : V ≤ R := Subgroup.map_subtype_le (W.comap Φ)
  have hXel : IsElemAbelian 3 XR := (hel.comap hΦinj).map R.subtype
  have hXcard : Nat.card XR = 3 ^ 4 := by
    change Nat.card ↥(Subgroup.map R.subtype (Subgroup.comap Φ X)) = 3 ^ 4
    have h1 : Nat.card ((X.comap Φ).map Φ) = Nat.card (X.comap Φ) :=
      Subgroup.card_map_of_injective hΦinj
    have h2 : (X.comap Φ).map Φ = X :=
      Subgroup.map_comap_eq_self (by rw [hΦrange]; exact hXI)
    have h3 : Nat.card (X.comap Φ) = Nat.card X := by rw [← h1, h2]
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective R), h3]
    exact hc
  have hW2 : IsPGroup 2 W := hU2.to_le inf_le_left
  have hV2 : IsPGroup 2 V := (hW2.comap_of_injective Φ hΦinj).map R.subtype
  have hVne : V ≠ ⊥ := by
    intro hV
    have hcomap : W.comap Φ = ⊥ := by
      have hiff := Subgroup.map_eq_bot_iff_of_injective (W.comap Φ)
        (Subgroup.subtype_injective R)
      exact hiff.1 (by simpa [V] using hV)
    have hWbot : W = ⊥ := by
      calc W = (W.comap Φ).map Φ := (Subgroup.map_comap_eq_self hWrange).symm
        _ = Subgroup.map Φ ⊥ := by rw [hcomap]
        _ = ⊥ := Subgroup.map_bot Φ
    exact hUI hWbot
  have hnorm : XR ≤ Subgroup.normalizer (V : Set (ModGL Tag.E6 Ω)) := by
    intro x hx
    obtain ⟨r, hrX, rfl⟩ := Subgroup.mem_map.1 hx
    have hXr : Φ r ∈ X := Subgroup.mem_comap.1 hrX
    have hInn : Φ r ∈ LayerSixE.twInndiagAut f := hXI hXr
    have hUnorm : Φ r ∈ Subgroup.normalizer (U : Set _) := hXU hXr
    have hInorm := Subgroup.le_normalizer (H := LayerSixE.twInndiagAut f) hInn
    have hmemV : ∀ v : ModGL Tag.E6 Ω, v ∈ V ↔ ∃ (hv : v ∈ R), Φ ⟨v, hv⟩ ∈ W := by
      intro v
      constructor
      · intro hv
        obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.1 hv
        exact ⟨r'.2, Subgroup.mem_comap.1 hr'⟩
      · rintro ⟨hv, hw⟩
        exact Subgroup.mem_map.2 ⟨⟨v, hv⟩, Subgroup.mem_comap.2 hw, rfl⟩
    have hconjV : ∀ v : ModGL Tag.E6 Ω,
        v ∈ V ↔ (r : ModGL Tag.E6 Ω) * v * (r : ModGL Tag.E6 Ω)⁻¹ ∈ V := by
      intro v
      rw [hmemV v, hmemV ((r : ModGL Tag.E6 Ω) * v * (r : ModGL Tag.E6 Ω)⁻¹)]
      constructor
      · rintro ⟨hv, hw⟩
        have hmul : (r : ModGL Tag.E6 Ω) * v * (r : ModGL Tag.E6 Ω)⁻¹ ∈ R :=
          mul_mem (mul_mem r.2 hv) (inv_mem r.2)
        refine ⟨hmul, ?_⟩
        have heq : (⟨(r : ModGL Tag.E6 Ω) * v * (r : ModGL Tag.E6 Ω)⁻¹, hmul⟩ : ↥R) =
            r * ⟨v, hv⟩ * r⁻¹ := Subtype.ext rfl
        rw [heq, map_mul, map_mul, map_inv]
        exact (ti_mem_inf_conj_iff hUnorm hInorm (Φ ⟨v, hv⟩)).1 hw
      · rintro ⟨hv', hw'⟩
        have hmul : (r : ModGL Tag.E6 Ω)⁻¹ *
            ((r : ModGL Tag.E6 Ω) * v * (r : ModGL Tag.E6 Ω)⁻¹) *
            (r : ModGL Tag.E6 Ω) ∈ R := mul_mem (mul_mem (inv_mem r.2) hv') r.2
        have hv : v ∈ R := by
          rwa [show (r : ModGL Tag.E6 Ω)⁻¹ *
              ((r : ModGL Tag.E6 Ω) * v * (r : ModGL Tag.E6 Ω)⁻¹) *
              (r : ModGL Tag.E6 Ω) = v by group] at hmul
        refine ⟨hv, ?_⟩
        have heq : (⟨(r : ModGL Tag.E6 Ω) * v * (r : ModGL Tag.E6 Ω)⁻¹, hv'⟩ : ↥R) =
            r * ⟨v, hv⟩ * r⁻¹ := Subtype.ext rfl
        rw [heq, map_mul, map_mul, map_inv] at hw'
        exact (ti_mem_inf_conj_iff hUnorm hInorm (Φ ⟨v, hv⟩)).2 hw'
    rw [Subgroup.mem_normalizer_iff]
    intro v
    simpa using hconjV v
  exact h82 hf h3 Ω Fr hFr hXR hVR hXel hXcard hVne hV2 hnorm

end CFSG.StandardType.NoOffTwE6Three

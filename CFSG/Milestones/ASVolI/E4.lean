module

public import CFSG.Quasithin.Background.RonanE43M12Main
public import CFSG.Quasithin.Background.RonanE43M22Three
public import CFSG.Quasithin.Background.RonanE43M23

public section

namespace CFSG.ASVolI

namespace ChE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3

abbrev fStarModO2 {G : Type} [Group G] (H : Subgroup G) :
    Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
  CFSG.generalizedFitting (↥H ⧸ CFSG.pCore 2 ↥H)

abbrev fStarPreO2 {G : Type} [Group G] (H : Subgroup G) : Subgroup G :=
  ((fStarModO2 H).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype

end ChE

open ChE CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3

@[expose] def E_4_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : G →* MulAut V, Function.Injective ρ → pCoreOf 2 (⊤ : Subgroup G) = ⊥ →
      ∀ T : Subgroup G, IsSylowIn 2 T ⊤ → Group.IsSolvable G → Even (Nat.card G) →
        aParam ρ.range = 1

set_option linter.unusedVariables false in
theorem as_E_4_1 : E_4_1 := fun G _ _ V _ _ hV ρ hρ hO2 T hT hsolv hev => by
  have hsolvR : Group.IsSolvable ↥ρ.range :=
    Group.isSolvable_of_surjective (f := ρ.rangeRestrict) ρ.rangeRestrict_surjective
  have h1 : CFSG.Open.pCore 2 G = ⊥ := by rw [← B6.pCoreOf_top]; exact hO2
  have h2 : CFSG.Open.pCore 2 ↥ρ.range = ⊥ := by
    have := CFSG.pCore_map_iso 2 (MonoidHom.ofInjective hρ)
    rw [h1, Subgroup.map_bot] at this
    exact this.symm
  have hev' : Even (Nat.card ρ.range) := by rw [← Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv]; exact hev
  exact E3.e4_1 hV hsolvR h2 hev'

@[expose] def E_4_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : G →* MulAut V, Function.Injective ρ → pCoreOf 2 (⊤ : Subgroup G) = ⊥ →
      ∀ (T L : Subgroup G) (Δ : Set (Subgroup G)), IsSylowIn 2 T ⊤ →
        L = CFSG.generalizedFitting G → CFSG.IsQuasisimple ↥L → L ⊔ T = ⊤ →
        (⨆ H ∈ Δ, H) = ⊤ →
        (∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarModO2 H) ∨
          ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarModO2 H) = p)) →
        (∀ H ∈ Δ, CFSG.IsQuasisimple ↥(fStarModO2 H) →
          H ≤ Subgroup.normalizer ((fStarPreO2 H ⊔ T : Subgroup G) : Set G)) →
        (∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) →
        aParam ρ.range ≤
          ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ),
            CFSG.Open.pRank 2 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))

theorem as_E_4_2 : E_4_2 :=
  fun G _ _ V _ _ hV ρ hρ hO2 T L Δ hT hLF hLq hLT hΔ hΔT hSpl hfix =>
    CFSG.Quasithin.RonanE42.e4_2_of_split G V hV ρ hρ hO2 T L Δ hT hLF hLq hLT hΔ hΔT hSpl hfix

@[expose] def E_4_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : G →* MulAut V, Function.Injective ρ → pCoreOf 2 (⊤ : Subgroup G) = ⊥ →
      ∀ (T L : Subgroup G), IsSylowIn 2 T ⊤ → fixV ρ.range < fixV (T.map ρ) →
        L = CFSG.generalizedFitting G → CFSG.IsQuasisimple ↥L →
        (IsSporadic .M12 (↥L ⧸ Subgroup.center ↥L) → aParam ρ.range ≤ 2) ∧
        (IsSporadic .M22 (↥L ⧸ Subgroup.center ↥L) ∨ IsSporadic .M24 (↥L ⧸ Subgroup.center ↥L) →
          aParam ρ.range ≤ 3) ∧
        (IsSporadic .M23 G →
          (MathieuCode23 ρ.range ⊤ ⊥ ∨ MathieuCocode23 ρ.range ⊤ ⊥) → aParam ρ.range ≤ 3)

section

theorem as_E_4_3 : E_4_3 := by
  intro G _ _ V _ _ _ ρ hρ hO2 T L hT hlt hLF hLq
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact CFSG.Quasithin.RonanE43.e43_M12 V ρ hρ hO2 hT hlt hLF hLq h
  · rintro (h | h)
    · exact CFSG.Quasithin.RonanE43.e43_M22_all V ρ hρ hO2 hT hlt hLF hLq h
    · exact CFSG.Quasithin.RonanE43.e43_M24 G V ρ hρ hO2 T L hT hlt hLF hLq h
  · intro _ h
    exact CFSG.Quasithin.RonanE43.aParam_le_three_of_mathieu23 h

end

end CFSG.ASVolI

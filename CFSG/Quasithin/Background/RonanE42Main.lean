module

public import CFSG.Quasithin.Background.RonanE42Core
public import CFSG.Quasithin.Background.RonanE42Group
public import CFSG.Quasithin.Background.RonanE42Om
public import CFSG.Quasithin.Background.RonanE42Rank
public import CFSG.Quasithin.Background.RonanE42Layer
public import CFSG.Quasithin.Background.RonanE42Prime

public section

namespace CFSG.Quasithin.RonanE42

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3

set_option linter.unusedVariables false in
theorem e4_2_of_goodW (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hΔ : (⨆ H ∈ Δ, H) = ⊤) (hΔT : ∀ H ∈ Δ, T ≤ H)
    (hgood : ∀ H ∈ Δ, ∀ Y : Subgroup G, Y ≤ H → (∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 H) →
      (∀ A : Subgroup G, Om ρ ((∑ᶠ (H' : Subgroup G) (_ : H' ∈ Δ),
          CFSG.Open.pRank 2 (⊤ : Subgroup (↥H' ⧸ CFSG.pCore 2 ↥H'))) + 1) A → A ≤ H → A ≤ Y) →
      H ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y))
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) :
    aParam ρ.range ≤ ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ),
      CFSG.Open.pRank 2 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  classical
  set c : Subgroup G → ℕ :=
    fun H => CFSG.Open.pRank 2 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) with hc
  have hΔfin : Δ.Finite := Set.toFinite Δ
  set Δf : Finset (Subgroup G) := hΔfin.toFinset with hΔf
  have hmemΔ : ∀ H, H ∈ Δf ↔ H ∈ Δ := fun H => hΔfin.mem_toFinset
  have hsum : (∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), c H) = ∑ H ∈ Δf, c H :=
    finsum_mem_eq_finite_toFinset_sum c hΔfin
  rw [hsum]
  set k := ∑ H ∈ Δf, c H with hk
  apply aParam_le_of_aSet_empty
  intro A' hA'
  let Ω : Set (Subgroup G) := {A | Om ρ (k + 1) A}
  have hA₀ : A'.comap ρ ∈ Ω := Om_comap_of_mem_aSet hρ hA'
  have hsetup : Setup ρ T Δf c Ω := by
    refine ⟨?_, ?_, ?_, hT, ?_, ?_, ?_⟩
    · intro A hA g
      exact Om_conjSubgroup hA g
    · intro A hA
      exact ⟨hA.1, hA.2.1, hA.2.2.1⟩
    · intro A hA B hBA hm
      exact hA.2.2.2 B hBA (Nat.lt_succ_of_le hm)
    · intro H hH
      exact hΔT H ((hmemΔ H).1 hH)
    · intro H hH B hBH hB2 hBc
      exact mQuot_inf_pCoreOf_le hBH hB2 hBc
    · intro H hH Y hYH hYn hYT hΩY
      refine hgood H ((hmemΔ H).1 hH) Y hYH hYn hYT fun A hA hAH => hΩY A ?_ hAH
      show Om ρ (k + 1) A
      rw [← hsum]
      exact hA
  have hgen : (⨆ H ∈ Δf, H) = ⊤ := by
    rw [eq_top_iff, ← hΔ]
    exact iSup₂_le fun H hH => le_iSup₂_of_le H ((hmemΔ H).2 hH) le_rfl
  have hL : ∀ W : Subgroup G, W ≤ T → W ≠ ⊥ → ⁅L, W⁆ = L := fun W hWT hW =>
    commutator_eq_of_quasisimple_fitting hLF hLq hO2 (hT.isPGroup.to_le hWT) hW
  have hcore := core hsetup hgen hA₀ hL
  obtain ⟨v, hv, l, hl, hne⟩ := hfix
  exact hne (hcore v hv l hl)

set_option linter.unusedVariables false in
theorem e4_2_of_good (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hΔ : (⨆ H ∈ Δ, H) = ⊤) (hΔT : ∀ H ∈ Δ, T ≤ H)
    (hgood : ∀ H ∈ Δ, ∀ Y : Subgroup G, Y ≤ H → (∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 H) → H ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y))
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) :
    aParam ρ.range ≤ ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ),
      CFSG.Open.pRank 2 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :=
  e4_2_of_goodW G V ρ hρ hO2 T L Δ hT hLF hLq hΔ hΔT
    (fun H hH Y hYH hYn hYT _ => hgood H hH Y hYH hYn hYT) hfix

set_option linter.unusedVariables false in
theorem e4_2_of_split (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hLT : L ⊔ T = ⊤) (hΔ : (⨆ H ∈ Δ, H) = ⊤)
    (hΔT : ∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p))
    (hSpl : ∀ H ∈ Δ, CFSG.IsQuasisimple ↥(fStarMod H) →
      H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G))
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) :
    aParam ρ.range ≤ ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ),
      CFSG.Open.pRank 2 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  refine e4_2_of_good G V ρ hρ hO2 T L Δ hT hLF hLq hΔ (fun H hH => (hΔT H hH).1)
    (fun H hH Y hYH hYn hYT => ?_) hfix
  obtain ⟨hTH, hF⟩ := hΔT H hH
  have hspl : H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) := by
    rcases hF with hq | hp
    · exact hSpl H hH hq
    · exact spl_of_prime hTH hp
  exact good_of_split hT hTH hF hspl hYH hYn hYT

end CFSG.Quasithin.RonanE42

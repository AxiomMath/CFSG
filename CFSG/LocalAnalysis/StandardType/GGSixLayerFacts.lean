module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsSL
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompCentre
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Tags

@[expose] def GGLayerCentreOddTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set G))) → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ E : Subgroup G, IsPGroup p E → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      E ≤ Subgroup.normalizer (G₀ : Set G) → (∀ e ∈ E, GGPsiInnerDiag (ggU t n f).D ψ e) →
        Odd (Nat.card (Subgroup.center
          ↥(LargeEvenLayer (G₀ ⊓ Subgroup.centralizer (E : Set G)))))

@[expose] def GGLayerPerfectTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set G))) → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ E : Subgroup G, IsPGroup p E → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      E ≤ Subgroup.normalizer (G₀ : Set G) → (∀ e ∈ E, GGPsiInnerDiag (ggU t n f).D ψ e) →
        ∀ X : Subgroup G, X ≤ G₀ ⊓ Subgroup.centralizer (E : Set G) → ⁅X, X⁆ = X →
          X ≤ LargeEvenLayer (G₀ ⊓ Subgroup.centralizer (E : Set G))

theorem ggLayerCentreOddInput_of_tags (h : ∀ t, GGLayerCentreOddTag t) :
    GGLayerCentreOddInput := by
  intro G _ _ t n f ψ G₀ hpres hodd p hp hp2 E hE hcomm hN hdiag
  exact h t G n f ψ G₀ hpres hodd p hp hp2 E hE hcomm hN hdiag

theorem ggLayerPerfectInput_of_tags (h : ∀ t, GGLayerPerfectTag t) : GGLayerPerfectInput := by
  intro G _ _ t n f ψ G₀ hpres hodd p hp hp2 E hE hcomm hN hdiag
  exact h t G n f ψ G₀ hpres hodd p hp hp2 E hE hcomm hN hdiag

theorem ggLayerTags_PSL : GGLayerCentreOddTag .PSL ∧ GGLayerPerfectTag .PSL := by
  refine ⟨fun G _ _ n f ψ G₀ hpres _ p hp hp2 E hE _ _ hdiag => ?_,
    fun G _ _ n f ψ G₀ hpres _ p hp hp2 E hE _ _ hdiag => ?_⟩ <;>
  · obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
    obtain ⟨-, -, hn, -⟩ := hadm
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← hrange]
    have hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ LinFusion.ggInducedPairs ψ := fun e he =>
      LinFusion.exists_mem_ggInducedPairs hrk ψ hker (hdiag e⁻¹ (E.inv_mem he))
    first
    | exact (LayerFacts.ggLayer_sl (F := GaloisField 2 f) hker hp hp2 hE hEA).1
    | exact (LayerFacts.ggLayer_sl (F := GaloisField 2 f) hker hp hp2 hE hEA).2

theorem ggLayerCentreOddTag_PSL : GGLayerCentreOddTag .PSL := ggLayerTags_PSL.1

theorem ggLayerPerfectTag_PSL : GGLayerPerfectTag .PSL := ggLayerTags_PSL.2

theorem ggLayerTags_of_placeholder (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGLayerCentreOddTag t ∧ GGLayerPerfectTag t := by
  refine ⟨fun G _ _ n f ψ G₀ hpres => ?_, fun G _ _ n f ψ G₀ hpres => ?_⟩ <;>
  · have hrk := hpres.1.2
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem ggLayerTags_POmegaOdd : GGLayerCentreOddTag .POmegaOdd ∧ GGLayerPerfectTag .POmegaOdd :=
  ⟨fun _ _ _ _ _ _ _ hpres => absurd rfl hpres.1.1.2.2.2,
    fun _ _ _ _ _ _ _ hpres => absurd rfl hpres.1.1.2.2.2⟩

theorem ggLayerInputs_of_remaining
    (hPSU : GGLayerCentreOddTag .PSU ∧ GGLayerPerfectTag .PSU)
    (hPSp : GGLayerCentreOddTag .PSp ∧ GGLayerPerfectTag .PSp)
    (hPlus : GGLayerCentreOddTag .POmegaPlus ∧ GGLayerPerfectTag .POmegaPlus)
    (hMinus : GGLayerCentreOddTag .POmegaMinus ∧ GGLayerPerfectTag .POmegaMinus)
    (hF4 : GGLayerCentreOddTag .F4 ∧ GGLayerPerfectTag .F4)
    (hE6 : GGLayerCentreOddTag .E6 ∧ GGLayerPerfectTag .E6)
    (hE7 : GGLayerCentreOddTag .E7 ∧ GGLayerPerfectTag .E7)
    (hE8 : GGLayerCentreOddTag .E8 ∧ GGLayerPerfectTag .E8)
    (hTwE6 : GGLayerCentreOddTag .twistedE6 ∧ GGLayerPerfectTag .twistedE6) :
    GGLayerCentreOddInput ∧ GGLayerPerfectInput := by
  have h : ∀ t, GGLayerCentreOddTag t ∧ GGLayerPerfectTag t := by
    intro t
    cases t with
    | PSL => exact ggLayerTags_PSL
    | PSU => exact hPSU
    | PSp => exact hPSp
    | POmegaOdd => exact ggLayerTags_POmegaOdd
    | POmegaPlus => exact hPlus
    | POmegaMinus => exact hMinus
    | F4 => exact hF4
    | E6 => exact hE6
    | E7 => exact hE7
    | E8 => exact hE8
    | twistedE6 => exact hTwE6
    | G2 => exact ggLayerTags_of_placeholder _ (Or.inl rfl)
    | trialityD4 => exact ggLayerTags_of_placeholder _ (Or.inr (Or.inl rfl))
    | twistedB2 => exact ggLayerTags_of_placeholder _ (Or.inr (Or.inr (Or.inl rfl)))
    | twistedG2 => exact ggLayerTags_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | twistedF4 =>
      exact ggLayerTags_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | Tits =>
      exact ggLayerTags_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  exact ⟨ggLayerCentreOddInput_of_tags fun t => (h t).1,
    ggLayerPerfectInput_of_tags fun t => (h t).2⟩

theorem ggSixCentreOddInput_of_remaining
    (hPSU : GGLayerCentreOddTag .PSU ∧ GGLayerPerfectTag .PSU)
    (hPSp : GGLayerCentreOddTag .PSp ∧ GGLayerPerfectTag .PSp)
    (hPlus : GGLayerCentreOddTag .POmegaPlus ∧ GGLayerPerfectTag .POmegaPlus)
    (hMinus : GGLayerCentreOddTag .POmegaMinus ∧ GGLayerPerfectTag .POmegaMinus)
    (hF4 : GGLayerCentreOddTag .F4 ∧ GGLayerPerfectTag .F4)
    (hE6 : GGLayerCentreOddTag .E6 ∧ GGLayerPerfectTag .E6)
    (hE7 : GGLayerCentreOddTag .E7 ∧ GGLayerPerfectTag .E7)
    (hE8 : GGLayerCentreOddTag .E8 ∧ GGLayerPerfectTag .E8)
    (hTwE6 : GGLayerCentreOddTag .twistedE6 ∧ GGLayerPerfectTag .twistedE6) :
    GGSixCentreOddInput :=
  have h := ggLayerInputs_of_remaining hPSU hPSp hPlus hMinus hF4 hE6 hE7 hE8 hTwE6
  ggSixCentreOddInput_of_layer h.1 h.2

end Tags

end CFSG.StandardType

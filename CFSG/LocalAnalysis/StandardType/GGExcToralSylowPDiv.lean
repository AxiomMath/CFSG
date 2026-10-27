module

public import CFSG.LocalAnalysis.StandardType.GGExcToralSylowLayer
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivExcRound

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Defs


@[expose] def GGExcPDivNonToralSylowRestInput (τ : Tag) : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ p : ℕ, p.Prime → p ≠ 2 →
    (p ∣ 2 ^ f - 1 ∧ p < excWeylBound τ ∨ p ∣ 2 ^ f + 1) →
    ∀ a : adjointGroup τ (GaloisField 2 f), a ^ p = 1 →
      ¬ GGExcToral τ (GaloisField 2 f) (Subgroup.zpowers a) →
        ¬ GGExcHighNonsplit τ (GaloisField 2 f) (Subgroup.zpowers a) →
          ∀ X : Subgroup (adjointGroup τ (GaloisField 2 f)),
            IsComponentOf X (Subgroup.centralizer {a}) → p ∣ Nat.card X

@[expose] def GGE6PDivNonToralSylowRestInput : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ p : ℕ, p.Prime → p ≠ 2 → (p ∣ 2 ^ f - 1 ∧ p < 7 ∨ p ∣ 2 ^ f + 1) →
    ∀ α ∈ LayerSixE.inndiagAut .E6 (GaloisField 2 f), α ^ p = 1 →
      ¬ LayerSixE.GGInndiagToral .E6 (GaloisField 2 f) (Subgroup.zpowers α) →
        ¬ GGE6InndiagHighNonsplit (GaloisField 2 f) (Subgroup.zpowers α) →
          ∀ X : Subgroup (adjointGroup .E6 (GaloisField 2 f)),
            IsComponentOf X (LayerSixE.autFix (Subgroup.zpowers α)) → p ∣ Nat.card X

theorem ggExcPDivNonToralSylowRestInput_of_rest {τ : Tag} (h : GGExcPDivNonToralRestInput τ) :
    GGExcPDivNonToralSylowRestInput τ := by
  intro f hf p hp hp2 hpq a ha ht hn X hX
  exact h f hf p hp hp2 (hpq.imp_left And.left) a ha ht hn X hX

theorem ggE6PDivNonToralSylowRestInput_of_rest (h : GGE6PDivNonToralRestInput) :
    GGE6PDivNonToralSylowRestInput := by
  intro f hf p hp hp2 hpq α hαD hαp ht hn X hX
  exact h f hf p hp hp2 (hpq.imp_left And.left) α hαD hαp ht hn X hX

end Defs

namespace ExcToralSylow

theorem dvd_and_lt_or_of_not_and {p m n b : ℕ} (h : p ∣ m ∨ p ∣ n) (hs : ¬ (p ∣ m ∧ b ≤ p)) :
    p ∣ m ∧ p < b ∨ p ∣ n :=
  h.imp_left fun hm => ⟨hm, not_le.mp fun hb => hs ⟨hm, hb⟩⟩

end ExcToralSylow

section Removal


theorem ggExcPDivNonToralRestInput_of_sylowRest {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (h : GGExcPDivNonToralSylowRestInput τ) :
    GGExcPDivNonToralRestInput τ := by
  intro f hf p hp hp2 hpq a ha ht hn X hX
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  by_cases hs : p ∣ 2 ^ f - 1 ∧ excWeylBound τ ≤ p
  · exact absurd (ExcToralSylow.ggExcToral_zpowers_of_splitCoprime hτ hp (by rw [hK]; exact hs.1)
      hs.2 ha) ht
  · exact h f hf p hp hp2 (ExcToralSylow.dvd_and_lt_or_of_not_and hpq hs) a ha ht hn X hX

theorem ggE6PDivNonToralRestInput_of_sylowRest (h : GGE6PDivNonToralSylowRestInput) :
    GGE6PDivNonToralRestInput := by
  intro f hf p hp hp2 hpq α hαD hαp ht hn X hX
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  by_cases hs : p ∣ 2 ^ f - 1 ∧ 7 ≤ p
  · exact absurd (ExcToralSylow.ggInndiagToral_E6_zpowers_of_splitCoprime hp hs.2
      (by rw [hK]; exact hs.1) hαD hαp) ht
  · exact h f hf p hp hp2 (ExcToralSylow.dvd_and_lt_or_of_not_and hpq hs) α hαD hαp ht hn X hX

@[expose] def GGLayerPDivExcRestSylow : Prop :=
  GGExcPDivNonToralSylowRestInput .F4 ∧ GGE6PDivNonToralSylowRestInput ∧
    GGExcPDivNonToralSylowRestInput .E7 ∧ GGExcPDivNonToralSylowRestInput .E8 ∧ GGTwE6PDivInput

theorem ggLayerPDivExcRest_of_sylow (h : GGLayerPDivExcRestSylow) : GGLayerPDivExcRest :=
  ⟨ggExcPDivNonToralRestInput_of_sylowRest (Or.inl rfl) h.1,
    ggE6PDivNonToralRestInput_of_sylowRest h.2.1,
    ggExcPDivNonToralRestInput_of_sylowRest (Or.inr (Or.inr (Or.inl rfl))) h.2.2.1,
    ggExcPDivNonToralRestInput_of_sylowRest (Or.inr (Or.inr (Or.inr rfl))) h.2.2.2.1, h.2.2.2.2⟩

theorem ggLayerPDivExcRestSylow_of_rest (h : GGLayerPDivExcRest) : GGLayerPDivExcRestSylow :=
  ⟨ggExcPDivNonToralSylowRestInput_of_rest h.1, ggE6PDivNonToralSylowRestInput_of_rest h.2.1,
    ggExcPDivNonToralSylowRestInput_of_rest h.2.2.1,
    ggExcPDivNonToralSylowRestInput_of_rest h.2.2.2.1, h.2.2.2.2⟩

end Removal

section Round

theorem ggLayerPDivRound6_of_excRestSylow (hlay : GGLayerTagsPilotRestSix)
    (h : GGLayerPDivExcRestSylow) : GGLayerPDivRound6 :=
  ggLayerPDivRound6_of_excRest hlay (ggLayerPDivExcRest_of_sylow h)

end Round

end CFSG.StandardType

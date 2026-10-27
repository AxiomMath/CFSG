module

public import CFSG.LocalAnalysis.StandardType.GGExcToralSylow
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEBundle

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Defs


@[expose] def GGExcAdjCoreNonToralSylowRestInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    (¬ p ∣ Nat.card K - 1 ∨ p < excWeylBound τ) →
    ∀ A : Subgroup ↥(adjointGroup τ K), IsPGroup p A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      ¬ GGExcToral τ K A → ¬ GGExcHighNonsplit τ K A →
        ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup τ K)),
          LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))) S

@[expose] def GGE6InndiagCoreNonToralSylowRestInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    (¬ p ∣ Nat.card K - 1 ∨ p < 7) →
    ∀ A : Subgroup (MulAut ↥(adjointGroup .E6 K)), IsPGroup p A →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A ≤ LayerSixE.inndiagAut .E6 K →
        ¬ LayerSixE.GGInndiagToral .E6 K A → ¬ GGE6InndiagHighNonsplit K A →
          ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup .E6 K)),
            LayerCores.IsSubCoreFamily (LayerSixE.autFix A) S

theorem ggExcAdjCoreNonToralSylowRestInput_of_rest {τ : Tag}
    (h : GGExcAdjCoreNonToralRestInput τ) : GGExcAdjCoreNonToralSylowRestInput τ :=
  fun K _ _ _ p hp hp2 _ => h K p hp hp2

theorem ggE6InndiagCoreNonToralSylowRestInput_of_rest (h : GGE6InndiagCoreNonToralRestInput) :
    GGE6InndiagCoreNonToralSylowRestInput :=
  fun K _ _ _ p hp hp2 _ => h K p hp hp2

end Defs

namespace ExcToralSylow

theorem not_dvd_or_lt_of_not_and {p m b : ℕ} (h : ¬ (p ∣ m ∧ b ≤ p)) : ¬ p ∣ m ∨ p < b :=
  (not_and_or.mp h).imp_right not_le.mp

end ExcToralSylow

section Removal


theorem ggExcAdjCoreNonToralRestInput_of_sylowRest {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (h : GGExcAdjCoreNonToralSylowRestInput τ) :
    GGExcAdjCoreNonToralRestInput τ := by
  intro K _ _ _ p hp hp2 A hA hAc ht hn
  by_cases hs : p ∣ Nat.card K - 1 ∧ excWeylBound τ ≤ p
  · exact absurd (ExcToralSylow.ggExcToral_of_splitCoprime hτ hp hs.1 hs.2 hA) ht
  · exact h K p hp hp2 (ExcToralSylow.not_dvd_or_lt_of_not_and hs) A hA hAc ht hn

theorem ggE6InndiagCoreNonToralRestInput_of_sylowRest
    (h : GGE6InndiagCoreNonToralSylowRestInput) : GGE6InndiagCoreNonToralRestInput := by
  intro K _ _ _ p hp hp2 A hA hAc hAD ht hn
  by_cases hs : p ∣ Nat.card K - 1 ∧ 7 ≤ p
  · exact absurd (ExcToralSylow.ggInndiagToral_E6_of_splitCoprime hp hs.2 hs.1 hAD hA) ht
  · exact h K p hp hp2 (ExcToralSylow.not_dvd_or_lt_of_not_and hs) A hA hAc hAD ht hn

@[expose] def GGLayerTagsPilotRestSixSylow : Prop :=
  GGExcAdjCoreNonToralSylowRestInput .F4 ∧
    (GGWeylFamQuotSolvInput .E7 ∧ GGExcAdjCoreNonToralSylowRestInput .E7) ∧
    (GGWeylFamQuotSolvInput .E8 ∧ GGExcAdjCoreNonToralSylowRestInput .E8) ∧
    (GGWeylFamQuotSolvInput .E6 ∧ GGE6InndiagCoreNonToralSylowRestInput) ∧
    GGTwE6InndiagCoreRestInput

theorem ggLayerTagsPilotRestSix_of_sylow (h : GGLayerTagsPilotRestSixSylow) :
    GGLayerTagsPilotRestSix :=
  ⟨ggExcAdjCoreNonToralRestInput_of_sylowRest (Or.inl rfl) h.1,
    ⟨h.2.1.1, ggExcAdjCoreNonToralRestInput_of_sylowRest (Or.inr (Or.inr (Or.inl rfl))) h.2.1.2⟩,
    ⟨h.2.2.1.1, ggExcAdjCoreNonToralRestInput_of_sylowRest (Or.inr (Or.inr (Or.inr rfl)))
      h.2.2.1.2⟩,
    ⟨h.2.2.2.1.1, ggE6InndiagCoreNonToralRestInput_of_sylowRest h.2.2.2.1.2⟩, h.2.2.2.2⟩

theorem ggLayerTagsPilotRestSixSylow_of_six (h : GGLayerTagsPilotRestSix) :
    GGLayerTagsPilotRestSixSylow :=
  ⟨ggExcAdjCoreNonToralSylowRestInput_of_rest h.1,
    ⟨h.2.1.1, ggExcAdjCoreNonToralSylowRestInput_of_rest h.2.1.2⟩,
    ⟨h.2.2.1.1, ggExcAdjCoreNonToralSylowRestInput_of_rest h.2.2.1.2⟩,
    ⟨h.2.2.2.1.1, ggE6InndiagCoreNonToralSylowRestInput_of_rest h.2.2.2.1.2⟩, h.2.2.2.2⟩

end Removal

end CFSG.StandardType

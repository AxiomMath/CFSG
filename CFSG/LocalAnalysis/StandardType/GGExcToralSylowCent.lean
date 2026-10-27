module

public import CFSG.LocalAnalysis.StandardType.GGExcToralSylowLayer
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsExcAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Defs


@[expose] def GGExcCentCompNonToralSylowInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ p : ℕ, p.Prime → p ≠ 2 → (¬ p ∣ Nat.card K - 1 ∨ p < excWeylBound τ) →
      ∀ s : ↥(adjointGroup τ K), s ^ p = 1 →
      ¬ GGExcToral τ K (Subgroup.zpowers s) →
      ∀ C : Subgroup ↥(adjointGroup τ K),
        IsComponentOf C (Subgroup.centralizer ({s} : Set ↥(adjointGroup τ K))) →
          GGNotExcThreeOrder (ggCQ C)

@[expose] def GGE6InndiagCompNonToralSylowInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ p : ℕ, p.Prime → p ≠ 2 → (¬ p ∣ Nat.card K - 1 ∨ p < 7) →
      ∀ α ∈ LayerSixE.inndiagAut .E6 K, α ^ p = 1 →
      ¬ LayerSixE.GGInndiagToral .E6 K (Subgroup.zpowers α) →
      ∀ X : Subgroup ↥(adjointGroup .E6 K),
        IsComponentOf X (LayerSixE.autFix (Subgroup.zpowers α)) → GGNotExcThreeOrder (ggCQ X)

theorem ggExcCentCompNonToralSylowInput_of_rest {τ : Tag} (h : GGExcCentCompNonToralInput τ) :
    GGExcCentCompNonToralSylowInput τ :=
  fun K _ _ _ hK4 p hp hp2 _ => h K hK4 p hp hp2

theorem ggE6InndiagCompNonToralSylowInput_of_rest (h : GGE6InndiagCompNonToralInput) :
    GGE6InndiagCompNonToralSylowInput :=
  fun K _ _ _ hK4 p hp hp2 _ => h K hK4 p hp hp2

end Defs

section Removal


theorem ggExcCentCompNonToralInput_of_sylowRest {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (h : GGExcCentCompNonToralSylowInput τ) :
    GGExcCentCompNonToralInput τ := by
  intro K _ _ _ hK4 p hp hp2 s hs ht C hC
  by_cases hsc : p ∣ Nat.card K - 1 ∧ excWeylBound τ ≤ p
  · exact absurd (ExcToralSylow.ggExcToral_zpowers_of_splitCoprime hτ hp hsc.1 hsc.2 hs) ht
  · exact h K hK4 p hp hp2 (ExcToralSylow.not_dvd_or_lt_of_not_and hsc) s hs ht C hC

theorem ggE6InndiagCompNonToralInput_of_sylowRest (h : GGE6InndiagCompNonToralSylowInput) :
    GGE6InndiagCompNonToralInput := by
  intro K _ _ _ hK4 p hp hp2 α hαD hαp ht X hX
  by_cases hsc : p ∣ Nat.card K - 1 ∧ 7 ≤ p
  · exact absurd (ExcToralSylow.ggInndiagToral_E6_zpowers_of_splitCoprime hp hsc.2 hsc.1 hαD hαp)
      ht
  · exact h K hK4 p hp hp2 (ExcToralSylow.not_dvd_or_lt_of_not_and hsc) α hαD hαp ht X hX

@[expose] def GGLayerNotExcThreeRestSylow : Prop :=
  GGExcSmallCompOrderInput ∧ GGExcCentCompNonToralSylowInput .F4 ∧
    GGExcCentCompNonToralSylowInput .E7 ∧ GGExcCentCompNonToralSylowInput .E8 ∧
    GGE6InndiagCompNonToralSylowInput ∧ GGTwE6InndiagCompInput

theorem ggLayerNotExcThreeRest_of_sylow (h : GGLayerNotExcThreeRestSylow) :
    GGLayerNotExcThreeRest :=
  ⟨h.1, ggExcCentCompNonToralInput_of_sylowRest (Or.inl rfl) h.2.1,
    ggExcCentCompNonToralInput_of_sylowRest (Or.inr (Or.inr (Or.inl rfl))) h.2.2.1,
    ggExcCentCompNonToralInput_of_sylowRest (Or.inr (Or.inr (Or.inr rfl))) h.2.2.2.1,
    ggE6InndiagCompNonToralInput_of_sylowRest h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem ggLayerNotExcThreeRestSylow_of_rest (h : GGLayerNotExcThreeRest) :
    GGLayerNotExcThreeRestSylow :=
  ⟨h.1, ggExcCentCompNonToralSylowInput_of_rest h.2.1,
    ggExcCentCompNonToralSylowInput_of_rest h.2.2.1,
    ggExcCentCompNonToralSylowInput_of_rest h.2.2.2.1,
    ggE6InndiagCompNonToralSylowInput_of_rest h.2.2.2.2.1, h.2.2.2.2.2⟩

end Removal

section Round

theorem ggLayerNotDFourTwoRound9_of_excRestSylow (hlay : GGLayerTagsPilotRestSix)
    (h : GGLayerNotExcThreeRestSylow) : GGLayerNotDFourTwoRound9 :=
  ggLayerNotDFourTwoRound9_of_excRest hlay (ggLayerNotExcThreeRest_of_sylow h)

theorem ggLayerNotUFourAltSixRound9_of_excRestSylow (hlay : GGLayerTagsPilotRestSix)
    (h : GGLayerNotExcThreeRestSylow) : GGLayerNotUFourAltSixRound9 :=
  ggLayerNotUFourAltSixRound9_of_excRest hlay (ggLayerNotExcThreeRest_of_sylow h)

end Round

end CFSG.StandardType

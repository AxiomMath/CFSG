module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
import CFSG.Adapters.TauCetiExceptional.BridgeTransport

public section

namespace CFSG.StandardType.GGSixE6Two

theorem lieModel_of_ggHasLabel_E6 {X : Type} [Group X] (h : GGHasLabel ⟨.E6, 0, 1⟩ X) :
    CFSG.Blueprint.LieModel X .E6 0 2 1 := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := h
  refine CFSG.Blueprint.LieModel.of_mulEquiv e.symm ?_
  exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, le_rfl, rfl⟩,
    untwistedChevalleyModel_largeEven .E6 hK⟩)

section Label

theorem nonempty_mulEquiv_EC_of_ggHasLabel {X : Type} [Group X]
    (h : GGHasLabel ⟨.E6, 0, 1⟩ X) : Nonempty (X ≃* EC) := by
  rcases lieModel_of_ggHasLabel_E6 h with ⟨hc, -⟩ | ⟨-, -, hE⟩ | ⟨-, hr, -⟩ | ⟨-, hb, -⟩
  · exact absurd hc (by decide)
  · rcases hE with ⟨-, hU⟩
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hU
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hcenK : Subgroup.center (CFSG.Blueprint.Chevalley.adjointGroup .E6 K) = ⊥ :=
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := Fintype.ofFinite K
    haveI : Fintype (GaloisField 2 1) := Fintype.ofFinite _
    have hcardF : Fintype.card (GaloisField 2 1) = 2 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num)]
      norm_num
    have hcardK : Fintype.card K = 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hK2
    have hcard : Fintype.card K = Fintype.card (GaloisField 2 1) := by rw [hcardK, hcardF]
    let σ : K ≃+* GaloisField 2 1 := FiniteField.ringEquivOfCardEq hcard
    have q₀ : CFSG.Blueprint.AdjointQuotient .E6 K ≃* EC :=
      ((QuotientGroup.quotientMulEquivOfEq hcenK).trans QuotientGroup.quotientBot).trans
        (CFSG.TauCetiBridge.adjointGroupCongr (τ := .E6) σ)
    exact ⟨e.trans q₀⟩
  · exact absurd hr (by decide)
  · exact absurd hb (by decide)

end Label

end CFSG.StandardType.GGSixE6Two

end

module

public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Core
public import CFSG.LocalAnalysis.SectionRank.ExceptionalEvenCover
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

open CFSG CFSG.RankThree.PartTwo.Sec19

theorem idG2_holds :
    Census194IdG2 := by
  intro Y _ _ q hR hq2 hI
  obtain ⟨hv, ⟨e₁⟩⟩ := hI
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have h3 : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
  have h3' : 3 ≤ 2 ^ q.exponent := by rw [← hcard]; exact h3
  have hK : Nat.card (GaloisField 2 q.exponent) = 2 ^ q.exponent :=
    GaloisField.card 2 q.exponent (by omega)
  obtain ⟨e₂⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq2 _ (hK.trans hcard.symm)
  have hM : CFSG.Blueprint.UntwistedChevalleyModel (Y ⧸ Subgroup.center Y)
      CFSG.Blueprint.Chevalley.Tag.G2 (2 ^ q.exponent) :=
    ⟨GaloisField 2 q.exponent, inferInstance, inferInstance, hK, ⟨e₁.trans e₂.symm⟩⟩
  have hS : CFSG.Blueprint.ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .G2 2 q.exponent :=
    ⟨⟨Nat.prime_two, hf, rfl, h3'⟩, hM⟩
  haveI : Group.IsPerfect Y := hR.quasisimple.1
  have hcen : Subgroup.center Y = ⊥ := by
    have hker := CFSG.SectionRank.g2_even_perfect_odd_cover_trivial hS
      (QuotientGroup.mk' (Subgroup.center Y)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' (Subgroup.center Y)).le
      (by rw [QuotientGroup.ker_mk']; exact odd_card_center_of_pCore_eq_bot hR.pCore_two)
    rwa [QuotientGroup.ker_mk'] at hker
  have hZ : Subgroup.center (CFSG.Blueprint.Chevalley.adjointGroup .G2
      (GaloisField 2 q.exponent)) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let eY : Y ≃* CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 q.exponent) :=
    (mulEquivQuotientCenterOfEqBot hcen).trans ((e₁.trans e₂.symm).trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
  exact Or.inl ⟨q.exponent, hf, Or.inr (Or.inr (Or.inr
    ⟨GaloisField 2 q.exponent, inferInstance, inferInstance, hK, ⟨eY⟩⟩))⟩

end CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

module

public import CFSG.YGroups.Y433.Bound
public import CFSG.Sporadic.Bridge.BPresentation
public import CFSG.Sporadic.Bridge.BSurj
public import CFSG.Sporadic.B
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.Monster.Existence

open CFSG.YGroups

theorem nonempty_B433_mulEquiv_nativeB
    : Nonempty (B433 ≃* CFSG.Blueprint.NativeSporadic.B) := by
  obtain ⟨hfin, hcard⟩ := B433_finite_card_le
  obtain ⟨hfinB, hcardB⟩ := CFSG.Sporadic.Bridge.B.finite_card_le_of_B433 hfin hcard
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.B.nonempty_mulEquiv_of_card_le hfinB hcardB
  have hsurj : Function.Surjective CFSG.Sporadic.Bridge.B.b433Hom :=
    CFSG.Sporadic.Bridge.B.b433Hom_surjective
  have h1 : Nat.card TauCeti.SporadicName.B.Group ≤ Nat.card B433 :=
    Nat.card_le_card_of_surjective _ hsurj
  have h2 : Nat.card TauCeti.SporadicName.B.Group = Nat.card CFSG.Blueprint.NativeSporadic.B :=
    (Nat.card_congr e.toEquiv).symm
  have h3 := CFSG.Sporadic.Bridge.B.card_le_card_B
  have h4 : Nat.card B433 ≤ Nat.card TauCeti.SporadicName.B.Group := by omega
  have : Finite B433 := hfin
  have hbij : Function.Bijective CFSG.Sporadic.Bridge.B.b433Hom :=
    hsurj.bijective_of_nat_card_le h4
  exact ⟨(MulEquiv.ofBijective _ hbij).trans e.symm⟩

theorem finite_B433 :
    Finite B433 := B433_finite_card_le.1

theorem isSimpleGroup_B433
    : IsSimpleGroup B433 := by
  obtain ⟨e⟩ := nonempty_B433_mulEquiv_nativeB
  exact @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.B.fam_b_simplicity e

theorem natCard_B433_eq
    : Nat.card B433 = Nat.card CFSG.Blueprint.NativeSporadic.B := by
  obtain ⟨e⟩ := nonempty_B433_mulEquiv_nativeB
  exact Nat.card_congr e.toEquiv

end CFSG.Monster.Existence

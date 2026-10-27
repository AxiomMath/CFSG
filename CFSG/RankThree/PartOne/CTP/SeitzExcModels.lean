module

import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.Adapters.TauCetiExceptional.ReeBridge
public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki

public section

namespace CFSG.RankThree.PartOne.CTP

open TauCeti CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem reeTitsModel_tits
    {S : Type} [Group S] (hiso : IsoLie S .tits) :
    ReeTitsModel S .Tits 2 1 := by
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  let e : S ≃* ValidLieTypeIndex.Group ⟨.tits, hv⟩ := e0
  have hfin : ∀ d : TitsLieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : TitsLieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin TitsLieIndex.of
  have := hchar TitsLieIndex.of
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_tits TitsLieIndex.of
  exact ⟨⟨Nat.prime_two, le_rfl, ⟨rfl, rfl, rfl⟩⟩, 0, rfl,
    ⟨TitsLieIndex.of.1.fixedField, inferInstance, inferInstance,
      (CFSG.TauCetiBridge.ReeF4.card_fixedField_tits _).trans (pow_one 2).symm,
      ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv 0).symm⟩⟩⟩

theorem reeTitsModel_reeG2
    {S : Type} [Group S] (a : ℕ)
    (hiso : IsoLie S (.reeG2 a)) : ReeTitsModel S .twistedG2 3 (2 * a + 1) := by
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  let e : S ≃* ValidLieTypeIndex.Group ⟨.reeG2 a, hv⟩ := e0
  have ha : 1 ≤ a := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa [LieTypeIndex.inStandardRange_iff] using h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.reeG2Bridge a hv (GaloisField 3 (2 * a + 1)) hK
  exact ⟨⟨Nat.prime_three, by omega, ⟨rfl, rfl, ⟨a, rfl⟩, by omega⟩⟩, a, rfl,
    ⟨GaloisField 3 (2 * a + 1), inferInstance, inferInstance, hK, ⟨e.trans φ.symm⟩⟩⟩

theorem suzukiModel_of_isoLie {S : Type} [Group S] (m : ℕ) (hiso : IsoLie S (.suzuki m)) :
    SuzukiModel S 2 (2 * m + 1) := by
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  exact CFSG.SectionRank.suzukiModel_of_mulEquiv e0
    (CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv)

end CFSG.RankThree.PartOne.CTP

module

public import CFSG.RankThree.PartOne.CTP.StrongPBridge
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.Adapters.TauCetiExceptional.ReeBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki

public section

namespace CFSG.RankThree.PartOne.CTP

open TauCeti CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem bridgeTuple_of_chevalley {S : Type} [Group S] {d : LieTypeIndex} {t : StatedLieTag}
    {p f : ℕ} (ht : t ∈ chevalleyExceptionalTags) (hp : p = d.characteristic)
    (h : ChevalleyExceptionalModel S t p f) : BridgeTuple S d := by
  refine ⟨t, 0, p, f, h.1, Or.inr (Or.inl ⟨rfl, ht, h⟩), hp, fun hh => ?_, fun hh => ?_⟩
  · rw [hh.1] at ht
    simp [chevalleyExceptionalTags] at ht
  · rw [hh.1] at ht
    simp [chevalleyExceptionalTags] at ht

theorem bridgeTuple_of_reeTits {S : Type} [Group S] {d : LieTypeIndex} {t : StatedLieTag}
    {p f : ℕ} (ht : t ∈ reeTitsTags) (hp : p = d.characteristic)
    (hT : (t = .Tits ∧ 0 = 0 ∧ p = 2 ∧ f = 1) → d = .tits)
    (h : ReeTitsModel S t p f) : BridgeTuple S d := by
  refine ⟨t, 0, p, f, h.1, Or.inr (Or.inr (Or.inl ⟨rfl, ht, h⟩)), hp, hT, fun hh => ?_⟩
  rw [hh.1] at ht
  simp [reeTitsTags] at ht

theorem bridgeTuple_of_suzuki {S : Type} [Group S] {m : ℕ} (hm : 1 ≤ m)
    (h : SuzukiModel S 2 (2 * m + 1)) : BridgeTuple S (.suzuki m) := by
  refine ⟨.twistedB2, 0, 2, 2 * m + 1,
    ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩,
    Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩)), by simp, (fun hh => nomatch hh.1), fun hh => ?_⟩
  have : 2 * m + 1 = 5 := hh.2.2.2
  have hm2 : m = 2 := by omega
  subst hm2
  rfl

section Models


theorem seitzBridgeRest : SeitzBridgeRest := by
  intro S _ d hiso hd
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  let e : S ≃* ValidLieTypeIndex.Group ⟨d, hv⟩ := e0
  cases d with
  | A r q => exact absurd trivial hd
  | twistedA r q => exact absurd trivial hd
  | C r q => exact absurd trivial hd
  | B r q =>
    have hr : 2 ≤ r :=
      ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
    have hr3 : 3 ≤ r := by
      by_contra h
      exact hd (show r = 2 by omega)
    by_cases hp : q.p = 2
    · exact bridgeTuple_of_classical (by simp [classicalTags]) (by simp)
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr3 e)
    · exact bridgeTuple_of_classical (by simp [classicalTags]) (by simp)
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp hr3 e)
  | D r q =>
    exact bridgeTuple_of_classical (by simp [classicalTags]) (by simp)
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e)
  | twistedD r q =>
    exact bridgeTuple_of_classical (by simp [classicalTags]) (by simp)
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e)
  | E6 q =>
    by_cases hq : q.p = 2
    · exact bridgeTuple_of_chevalley (t := .E6) (p := q.p) (f := q.exponent)
        (by simp [chevalleyExceptionalTags]) (by simp)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
            CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e6 q hv hq e⟩
    · exact bridgeTuple_of_chevalley (t := .E6) (p := q.p) (f := q.exponent)
        (by simp [chevalleyExceptionalTags]) (by simp)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.e6 q hv
            hq e⟩
  | E7 q =>
    by_cases hq : q.p = 2
    · exact bridgeTuple_of_chevalley (t := .E7) (p := q.p) (f := q.exponent)
        (by simp [chevalleyExceptionalTags]) (by simp)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
            CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e7 q hv hq e⟩
    · exact bridgeTuple_of_chevalley (t := .E7) (p := q.p) (f := q.exponent)
        (by simp [chevalleyExceptionalTags]) (by simp)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.e7 q hv
            hq e⟩
  | E8 q =>
    by_cases hq : q.p = 2
    · exact bridgeTuple_of_chevalley (t := .E8) (p := q.p) (f := q.exponent)
        (by simp [chevalleyExceptionalTags]) (by simp)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
            CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e8 q hv hq e⟩
    · exact bridgeTuple_of_chevalley (t := .E8) (p := q.p) (f := q.exponent)
        (by simp [chevalleyExceptionalTags]) (by simp)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.e8 q hv
            hq e⟩
  | F4 q =>
    by_cases hq : q.p = 2
    · exact bridgeTuple_of_chevalley (t := .F4) (p := q.p) (f := q.exponent)
        (by simp [chevalleyExceptionalTags]) (by simp)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
            CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 q hv hq e⟩
    · exact bridgeTuple_of_chevalley (t := .F4) (p := q.p) (f := q.exponent)
        (by simp [chevalleyExceptionalTags]) (by simp)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.f4 q hv
            hq e⟩
  | G2 q =>
    have h3 : 3 ≤ q.p ^ q.exponent := by
      have h := ((LieTypeIndex.valid_iff _).1 hv).1
      simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using h
    by_cases hq : q.p = 2
    · exact bridgeTuple_of_chevalley (t := .G2) (p := q.p) (f := q.exponent)
        (by simp [chevalleyExceptionalTags]) (by simp)
        ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩,
          CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
            CFSG.TauCetiBridge.Even.chevalleyBridgesEven.g2 q hv hq e⟩
    · exact bridgeTuple_of_chevalley (t := .G2) (p := q.p) (f := q.exponent)
        (by simp [chevalleyExceptionalTags]) (by simp)
        ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩,
          CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.g2 q hv
            hq e⟩
  | twistedE6 q =>
    by_cases hq : q.p = 2
    · exact bridgeTuple_of_chevalley (t := .twistedE6) (p := q.p) (f := q.exponent)
        (by simp [chevalleyExceptionalTags]) (by simp)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
            CFSG.TauCetiBridge.Even.chevalleyBridgesEven.twistedE6 q hv hq (by decide) e⟩
    · exact bridgeTuple_of_chevalley (t := .twistedE6) (p := q.p) (f := q.exponent)
        (by simp [chevalleyExceptionalTags]) (by simp)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.twistedModel_of_bridge
            CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv hq (by decide) e⟩
  | trialityD4 q =>
    by_cases hq : q.p = 2
    · exact bridgeTuple_of_chevalley (t := .trialityD4) (p := q.p) (f := q.exponent)
        (by simp [chevalleyExceptionalTags]) (by simp)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
            CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide) e⟩
    · exact bridgeTuple_of_chevalley (t := .trialityD4) (p := q.p) (f := q.exponent)
        (by simp [chevalleyExceptionalTags]) (by simp)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.twistedModel_of_bridge
            CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hq (by decide) e⟩
  | suzuki m =>
    have hm : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
    exact bridgeTuple_of_suzuki hm (CFSG.SectionRank.suzukiModel_of_mulEquiv e
      (CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv))
  | reeG2 a =>
    have ha : 1 ≤ a := by
      have h := ((LieTypeIndex.valid_iff _).1 hv).1
      simpa [LieTypeIndex.inStandardRange_iff] using h
    have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
      GaloisField.card 3 (2 * a + 1) (by omega)
    obtain ⟨φ⟩ := CFSG.TauCetiBridge.reeG2Bridge a hv (GaloisField 3 (2 * a + 1)) hK
    exact bridgeTuple_of_reeTits (t := .twistedG2) (p := 3) (f := 2 * a + 1)
      (by simp [reeTitsTags]) (by simp) (fun hh => nomatch hh.1)
      ⟨⟨Nat.prime_three, by omega, ⟨rfl, rfl, ⟨a, rfl⟩, by omega⟩⟩, a, rfl,
        ⟨GaloisField 3 (2 * a + 1), inferInstance, inferInstance, hK, ⟨e.trans φ.symm⟩⟩⟩
  | reeF4 m =>
    have hfin : ∀ d : ReeF4LieIndex, Finite d.1.fixedField := fun _ => inferInstance
    have hchar : ∀ d : ReeF4LieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
    have := hfin (ReeF4LieIndex.of m hv)
    have := hchar (ReeF4LieIndex.of m hv)
    have hm : 1 ≤ m :=
      (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
    have hhalf : (ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
      SuzukiReeIndex.halfExponent_reeF4 m hv
    obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_reeF4 (ReeF4LieIndex.of m hv)
    rw [hhalf] at e₁
    have hK := CFSG.TauCetiBridge.ReeF4.card_fixedField_reeF4 (ReeF4LieIndex.of m hv)
    rw [hhalf] at hK
    exact bridgeTuple_of_reeTits (t := .twistedF4) (p := 2) (f := 2 * m + 1)
      (by simp [reeTitsTags]) (by simp) (fun hh => nomatch hh.1)
      ⟨⟨Nat.prime_two, by omega, ⟨rfl, rfl, ⟨m, rfl⟩, by omega⟩⟩, m, rfl,
        ⟨(ReeF4LieIndex.of m hv).1.fixedField, inferInstance, inferInstance, hK,
          ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv m).symm⟩⟩⟩
  | tits =>
    have hfin : ∀ d : TitsLieIndex, Finite d.1.fixedField := fun _ => inferInstance
    have hchar : ∀ d : TitsLieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
    have := hfin TitsLieIndex.of
    have := hchar TitsLieIndex.of
    obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_tits TitsLieIndex.of
    exact bridgeTuple_of_reeTits (t := .Tits) (p := 2) (f := 1)
      (by simp [reeTitsTags]) (by simp) (fun _ => rfl)
      ⟨⟨Nat.prime_two, le_rfl, ⟨rfl, rfl, rfl⟩⟩, 0, rfl,
        ⟨TitsLieIndex.of.1.fixedField, inferInstance, inferInstance,
          (CFSG.TauCetiBridge.ReeF4.card_fixedField_tits _).trans (pow_one 2).symm,
          ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv 0).symm⟩⟩⟩

theorem seitzBridge : SeitzBridge := seitzBridge_of_rest seitzBridgeRest

end Models

end CFSG.RankThree.PartOne.CTP

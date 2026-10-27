module

public import CFSG.RankThree.PartTwo.KFacts.KS14SzClassical
public import CFSG.RankThree.PartTwo.KFacts.KS14SzRee
public import CFSG.RankThree.Chevalley.ExceptionalModelOrderThree
public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.Adapters.TauCetiExceptional.ReeBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open TauCeti CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem three_dvd_card_or_suzukiModel_of_lie (d : ValidLieTypeIndex) {G : Type} [Group G]
    [Finite G] (e : G ≃* d.Group) : 3 ∣ Nat.card G ∨ ∃ f : ℕ, SuzukiModel G 2 f := by
  obtain ⟨d, hv⟩ := d
  have hcl : ∀ {t : StatedLieTag} {n p f : ℕ}, StatedClassicalModel G t n p f →
      3 ∣ Nat.card G ∨ ∃ f : ℕ, SuzukiModel G 2 f :=
    fun h => .inl (classicalModel_exists_orderOf_eq_three h).2
  have hex : ∀ {t : StatedLieTag} {p f : ℕ}, ChevalleyExceptionalModel G t p f →
      3 ∣ Nat.card G ∨ ∃ f : ℕ, SuzukiModel G 2 f :=
    fun h => .inl (CFSG.RankThree.Chevalley.Chevalley_exceptional_models_order_divisible_by_three
      G _ _ _ h)
  have hree : ∀ {t : StatedLieTag} {p f : ℕ}, ReeTitsModel G t p f →
      3 ∣ Nat.card G ∨ ∃ f : ℕ, SuzukiModel G 2 f :=
    fun h => .inl (three_dvd_card_of_reeTitsModel h)
  cases d with
  | A r q =>
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hr : 1 ≤ r :=
      ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
    obtain ⟨y, hy⟩ := exists_orderOf_eq_three_statedProj_statedSL
      (K := GaloisField q.p q.exponent) (n := r + 1) (by omega)
    let φ := (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)).trans
      (projectiveSpecialLinearGroupEquivStatedProj (r + 1) (GaloisField q.p q.exponent))
    refine .inl ?_
    rw [← hy, ← MulEquiv.orderOf_eq φ.symm]
    exact orderOf_dvd_natCard _
  | twistedA r q => exact hcl (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)
  | B r q =>
    have hr : 2 ≤ r :=
      ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact hcl (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)
    · by_cases hp : q.p = 2
      · exact hcl (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr3 e)
      · exact hcl (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp hr3 e)
  | C r q => exact hcl (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e)
  | D r q => exact hcl (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e)
  | twistedD r q =>
    exact hcl (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e)
  | E6 q =>
    by_cases hq : q.p = 2
    · exact hex (t := .E6) ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
          CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e6 q hv hq e⟩
    · exact hex (t := .E6) ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.e6 q hv
          hq e⟩
  | E7 q =>
    by_cases hq : q.p = 2
    · exact hex (t := .E7) ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
          CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e7 q hv hq e⟩
    · exact hex (t := .E7) ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.e7 q hv
          hq e⟩
  | E8 q =>
    by_cases hq : q.p = 2
    · exact hex (t := .E8) ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
          CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e8 q hv hq e⟩
    · exact hex (t := .E8) ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.e8 q hv
          hq e⟩
  | F4 q =>
    by_cases hq : q.p = 2
    · exact hex (t := .F4) ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
          CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 q hv hq e⟩
    · exact hex (t := .F4) ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.f4 q hv
          hq e⟩
  | G2 q =>
    have h3 : 3 ≤ q.p ^ q.exponent := by
      have h := ((LieTypeIndex.valid_iff _).1 hv).1
      simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using h
    by_cases hq : q.p = 2
    · exact hex (t := .G2) ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩,
        CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
          CFSG.TauCetiBridge.Even.chevalleyBridgesEven.g2 q hv hq e⟩
    · exact hex (t := .G2) ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩,
        CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.g2 q hv
          hq e⟩
  | twistedE6 q =>
    by_cases hq : q.p = 2
    · exact hex (t := .twistedE6) ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
          CFSG.TauCetiBridge.Even.chevalleyBridgesEven.twistedE6 q hv hq (by decide) e⟩
    · exact hex (t := .twistedE6) ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.twistedModel_of_bridge
          CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv hq (by decide) e⟩
  | trialityD4 q =>
    by_cases hq : q.p = 2
    · exact hex (t := .trialityD4) ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
          CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide) e⟩
    · exact hex (t := .trialityD4) ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.twistedModel_of_bridge
          CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hq (by decide) e⟩
  | suzuki m =>
    exact .inr ⟨2 * m + 1, CFSG.SectionRank.suzukiModel_of_mulEquiv e
      (CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv)⟩
  | reeG2 a =>
    have ha : 1 ≤ a := by
      have h := ((LieTypeIndex.valid_iff _).1 hv).1
      simpa [LieTypeIndex.inStandardRange_iff] using h
    have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
      GaloisField.card 3 (2 * a + 1) (by omega)
    obtain ⟨φ⟩ := CFSG.TauCetiBridge.reeG2Bridge a hv (GaloisField 3 (2 * a + 1)) hK
    exact hree (t := .twistedG2) (p := 3) (f := 2 * a + 1)
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
    exact hree (t := .twistedF4) (p := 2) (f := 2 * m + 1)
      ⟨⟨Nat.prime_two, by omega, ⟨rfl, rfl, ⟨m, rfl⟩, by omega⟩⟩, m, rfl,
        ⟨(ReeF4LieIndex.of m hv).1.fixedField, inferInstance, inferInstance, hK,
          ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv m).symm⟩⟩⟩
  | tits =>
    have hfin : ∀ d : TitsLieIndex, Finite d.1.fixedField := fun _ => inferInstance
    have hchar : ∀ d : TitsLieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
    have := hfin TitsLieIndex.of
    have := hchar TitsLieIndex.of
    obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_tits TitsLieIndex.of
    exact hree (t := .Tits) (p := 2) (f := 1)
      ⟨⟨Nat.prime_two, le_rfl, ⟨rfl, rfl, rfl⟩⟩, 0, rfl,
        ⟨TitsLieIndex.of.1.fixedField, inferInstance, inferInstance,
          (CFSG.TauCetiBridge.ReeF4.card_fixedField_tits _).trans (pow_one 2).symm,
          ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv 0).symm⟩⟩⟩

end CFSG.RankThree.PartTwo.KFacts.KS14

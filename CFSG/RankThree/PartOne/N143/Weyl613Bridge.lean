module

public import CFSG.RankThree.PartOne.N143.Weyl613Small
public import CFSG.RankThree.PartOne.N143.Inspect613Even
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint TauCeti
open CFSG.RankThree.PartOne.Census3 (IsoLie ThmThreeItem7 ThmThreeItem8 ThmThreeItem9)

theorem evenLieTypeSmall_of_model {X : Type} [Group X] {t : StatedLieTag} (ht : t ∈ classicalTags)
    {n p f : ℕ} (hp : p = 2) (hm : StatedClassicalModel X t n p f) (hs : SmallEvenParams t n f) :
    EvenLieTypeSmall X := by
  subst hp
  exact ⟨t, n, f, hm.1, Or.inl ⟨ht, hm⟩, hs⟩

theorem evenLieTypeSmall_of_chevalley {X : Type} [Group X] {t : StatedLieTag}
    (ht : t ∈ chevalleyExceptionalTags) {p f : ℕ} (hp : p = 2)
    (hm : ChevalleyExceptionalModel X t p f) (hs : SmallEvenParams t 0 f) : EvenLieTypeSmall X := by
  subst hp
  exact ⟨t, 0, f, hm.1, Or.inr (Or.inl ⟨rfl, ht, hm⟩), hs⟩

theorem evenLieTypeSmall_of_reeTits {X : Type} [Group X] {t : StatedLieTag}
    (ht : t ∈ reeTitsTags) {p f : ℕ} (hp : p = 2) (hm : ReeTitsModel X t p f)
    (hs : SmallEvenParams t 0 f) : EvenLieTypeSmall X := by
  subst hp
  exact ⟨t, 0, f, hm.1, Or.inr (Or.inr (Or.inl ⟨rfl, ht, hm⟩)), hs⟩

theorem small_A {X : Type} [Group X] (r : ℕ) (q : PrimePower) (hq : q.p = 2)
    (hs : SmallEvenParams .PSL (r + 1) q.exponent) (h : IsoLie X (.A r q)) : EvenLieTypeSmall X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  exact evenLieTypeSmall_of_model (by simp [classicalTags]) hq
    (statedClassicalModel_of_isoLie_A hv e) hs

theorem small_twistedA {X : Type} [Group X] (r : ℕ) (q : PrimePower) (hq : q.p = 2)
    (hs : SmallEvenParams .PSU (r + 1) q.exponent) (h : IsoLie X (.twistedA r q)) :
    EvenLieTypeSmall X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  exact evenLieTypeSmall_of_model (by simp [classicalTags]) hq
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e) hs

theorem small_B {X : Type} [Group X] (r : ℕ) (q : PrimePower) (hq : q.p = 2) (hr : 2 ≤ r)
    (hs : r ≤ 4) (h : IsoLie X (.B r q)) : EvenLieTypeSmall X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  rcases Nat.lt_or_ge r 3 with h2 | h3
  · obtain rfl : r = 2 := by omega
    exact evenLieTypeSmall_of_model (by simp [classicalTags]) hq
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e) (by simp [SmallEvenParams])
  · exact evenLieTypeSmall_of_model (by simp [classicalTags]) hq
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq h3 e)
      (by simpa [SmallEvenParams] using hs)

theorem small_D {X : Type} [Group X] (q : PrimePower) (hq : q.p = 2) (h : IsoLie X (.D 4 q)) :
    EvenLieTypeSmall X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  exact evenLieTypeSmall_of_model (by simp [classicalTags]) hq
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even 4 q hv hq e)
    (by simp [SmallEvenParams])

theorem small_twistedD {X : Type} [Group X] (q : PrimePower) (hq : q.p = 2)
    (h : IsoLie X (.twistedD 4 q)) : EvenLieTypeSmall X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  exact evenLieTypeSmall_of_model (by simp [classicalTags]) hq
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 q hv hq e)
    (by simp [SmallEvenParams])

theorem small_suzuki {X : Type} [Group X] (m : ℕ) (h : IsoLie X (.suzuki m)) :
    EvenLieTypeSmall X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  have hm1 : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hm := CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
  have hm' : CFSG.Blueprint.SuzukiModel X 2 (2 * m + 1) := by
    obtain ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e'⟩⟩ := hm
    exact ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e.trans e'⟩⟩
  exact ⟨.twistedB2, 0, 2 * m + 1, ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩,
    Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hm'⟩)), trivial⟩

section Models


theorem small_G2 {X : Type} [Group X] (q : PrimePower) (hq : q.p = 2)
    (h : IsoLie X (.G2 q)) : EvenLieTypeSmall X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  have h3 : 3 ≤ q.p ^ q.exponent := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using h
  exact evenLieTypeSmall_of_chevalley (t := .G2) (by simp [chevalleyExceptionalTags]) hq
    ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.g2 q hv hq e⟩ trivial

theorem small_F4 {X : Type} [Group X] (q : PrimePower) (hq : q.p = 2) (hf : q.exponent = 1)
    (h : IsoLie X (.F4 q)) : EvenLieTypeSmall X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  exact evenLieTypeSmall_of_chevalley (t := .F4) (by simp [chevalleyExceptionalTags]) hq
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 q hv hq e⟩ hf

theorem small_trialityD4 {X : Type} [Group X] (q : PrimePower) (hq : q.p = 2)
    (h : IsoLie X (.trialityD4 q)) : EvenLieTypeSmall X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  exact evenLieTypeSmall_of_chevalley (t := .trialityD4) (by simp [chevalleyExceptionalTags]) hq
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide) e⟩ trivial

theorem small_reeF4 {X : Type} [Group X] (m : ℕ) (h : IsoLie X (.reeF4 m)) :
    EvenLieTypeSmall X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
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
  exact evenLieTypeSmall_of_reeTits (t := .twistedF4) (by simp [reeTitsTags]) rfl
    ⟨⟨Nat.prime_two, by omega, ⟨rfl, rfl, ⟨m, rfl⟩, by omega⟩⟩, m, rfl,
      ⟨(ReeF4LieIndex.of m hv).1.fixedField, inferInstance, inferInstance, hK,
        ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv m).symm⟩⟩⟩ trivial

theorem small_tits {X : Type} [Group X] (h : IsoLie X .tits) : EvenLieTypeSmall X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  have hfin : ∀ d : TitsLieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : TitsLieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin TitsLieIndex.of
  have := hchar TitsLieIndex.of
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_tits TitsLieIndex.of
  exact evenLieTypeSmall_of_reeTits (t := .Tits) (by simp [reeTitsTags]) rfl
    ⟨⟨Nat.prime_two, le_rfl, ⟨rfl, rfl, rfl⟩⟩, 0, rfl,
      ⟨TitsLieIndex.of.1.fixedField, inferInstance, inferInstance,
        (CFSG.TauCetiBridge.ReeF4.card_fixedField_tits _).trans (pow_one 2).symm,
        ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv 0).symm⟩⟩⟩ trivial

theorem evenLieTypeSmall_of_item789 {X : Type} [Group X]
    (h : ThmThreeItem7 X ∨ ThmThreeItem8 X ∨ ThmThreeItem9 X) : EvenLieTypeSmall X := by
  rcases h with h7 | h8 | h9
  · rcases h7 with ⟨q, hq, hA⟩ | ⟨m, hS⟩ | ⟨q, hq, hrest⟩ | ⟨m, hR⟩ | hT
    · exact small_A 1 q hq (Or.inl (by norm_num)) hA
    · exact small_suzuki m hS
    · rcases hrest with hU2 | hA2 | hB2 | hG | hU3 | hU4 | hT
      · exact small_twistedA 2 q hq (Or.inl (by norm_num)) hU2
      · exact small_A 2 q hq (Or.inl (by norm_num)) hA2
      · exact small_B 2 q hq le_rfl (by norm_num) hB2
      · exact small_G2 q hq hG
      · exact small_twistedA 3 q hq (Or.inl (by norm_num)) hU3
      · exact small_twistedA 4 q hq (Or.inl (by norm_num)) hU4
      · exact small_trialityD4 q hq hT
    · exact small_reeF4 m hR
    · exact small_tits hT
  · obtain ⟨q, hq, hA | hB | hD⟩ := h8
    · exact small_A 3 q hq (Or.inl (by norm_num)) hA
    · exact small_B 3 q hq (by norm_num) (by norm_num) hB
    · exact small_twistedD q hq hD
  · obtain ⟨q, hq, hf, hA4 | hA5 | hA6 | hU5 | hB4 | hD4 | hF4⟩ := h9
    · exact small_A 4 q hq (Or.inl (by norm_num)) hA4
    · exact small_A 5 q hq (Or.inr ⟨Or.inl rfl, hf⟩) hA5
    · exact small_A 6 q hq (Or.inr ⟨Or.inr rfl, hf⟩) hA6
    · exact small_twistedA 5 q hq (Or.inr ⟨rfl, hf⟩) hU5
    · exact small_B 4 q hq (by norm_num) le_rfl hB4
    · exact small_D q hq hD4
    · exact small_F4 q hq hf hF4

end Models

end CFSG.RankThree.PartOne.N143

module

public import CFSG.RankThree.PartOne.N143.Inspect613
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
import CFSG.Adapters.LinearCatalogStated

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.Census3 TauCeti
open CFSG.Blueprint (classicalTags)

@[expose] def EvenExceptionalBridge : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ q : PrimePower, q.p = 2 ∧ (IsoLie X (.G2 q) ∨ IsoLie X (.trialityD4 q))) ∨
      (∃ m : ℕ, IsoLie X (.reeF4 m)) ∨ IsoLie X .tits ∨
      (∃ q : PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ IsoLie X (.F4 q))) →
    CFSG.Blueprint.EvenLieType X

theorem evenLieType_of_model {X : Type} [Group X] {t : StatedLieTag} (ht : t ∈ classicalTags)
    {n p f : ℕ} (hp : p = 2) (hm : StatedClassicalModel X t n p f) :
    CFSG.Blueprint.EvenLieType X := by
  subst hp
  exact ⟨t, n, f, hm.1, Or.inl ⟨ht, hm⟩⟩

theorem statedClassicalModel_of_isoLie_A {X : Type} [Group X] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.A r q).Valid) (e : X ≃* (CFSGIndex.lie ⟨.A r q, hv⟩).Group) :
    StatedClassicalModel X .PSL (r + 1) q.p q.exponent :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e

theorem evenLieType_of_isoLie_A {X : Type} [Group X] {r : ℕ} {q : PrimePower} (hq : q.p = 2)
    (h : IsoLie X (.A r q)) : CFSG.Blueprint.EvenLieType X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  exact evenLieType_of_model (by simp [classicalTags]) hq (statedClassicalModel_of_isoLie_A hv e)

theorem evenLieType_of_isoLie_twistedA {X : Type} [Group X] {r : ℕ} {q : PrimePower} (hq : q.p = 2)
    (h : IsoLie X (.twistedA r q)) : CFSG.Blueprint.EvenLieType X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  exact evenLieType_of_model (by simp [classicalTags]) hq
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)

theorem evenLieType_of_isoLie_B {X : Type} [Group X] {r : ℕ} {q : PrimePower} (hq : q.p = 2)
    (hr : 2 ≤ r) (h : IsoLie X (.B r q)) : CFSG.Blueprint.EvenLieType X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  rcases Nat.lt_or_ge r 3 with h2 | h3
  · obtain rfl : r = 2 := by omega
    exact evenLieType_of_model (by simp [classicalTags]) hq
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)
  · exact evenLieType_of_model (by simp [classicalTags]) hq
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq h3 e)

theorem evenLieType_of_isoLie_D {X : Type} [Group X] {r : ℕ} {q : PrimePower} (hq : q.p = 2)
    (h : IsoLie X (.D r q)) : CFSG.Blueprint.EvenLieType X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  exact evenLieType_of_model (by simp [classicalTags]) hq
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hq e)

theorem evenLieType_of_isoLie_twistedD {X : Type} [Group X] {r : ℕ} {q : PrimePower} (hq : q.p = 2)
    (h : IsoLie X (.twistedD r q)) : CFSG.Blueprint.EvenLieType X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  exact evenLieType_of_model (by simp [classicalTags]) hq
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hq e)

theorem evenLieType_of_isoLie_suzuki {X : Type} [Group X] {m : ℕ} (h : IsoLie X (.suzuki m)) :
    CFSG.Blueprint.EvenLieType X := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  have hm1 : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hm := CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
  have hm' : CFSG.Blueprint.SuzukiModel X 2 (2 * m + 1) := by
    obtain ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e'⟩⟩ := hm
    exact ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e.trans e'⟩⟩
  exact ⟨.twistedB2, 0, 2 * m + 1, ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩,
    Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hm'⟩))⟩

theorem evenListBridge_of_exceptional (hX : EvenExceptionalBridge) : EvenListBridge := by
  intro X _ _ h
  rcases h with h7 | h8 | h9
  · rcases h7 with ⟨q, hq, hA⟩ | ⟨m, hS⟩ | ⟨q, hq, hrest⟩ | ⟨m, hR⟩ | hT
    · exact evenLieType_of_isoLie_A hq hA
    · exact evenLieType_of_isoLie_suzuki hS
    · rcases hrest with hU2 | hA2 | hB2 | hG | hU3 | hU4 | hT
      · exact evenLieType_of_isoLie_twistedA hq hU2
      · exact evenLieType_of_isoLie_A hq hA2
      · exact evenLieType_of_isoLie_B hq (by norm_num) hB2
      · exact hX X (Or.inl ⟨q, hq, Or.inl hG⟩)
      · exact evenLieType_of_isoLie_twistedA hq hU3
      · exact evenLieType_of_isoLie_twistedA hq hU4
      · exact hX X (Or.inl ⟨q, hq, Or.inr hT⟩)
    · exact hX X (Or.inr (Or.inl ⟨m, hR⟩))
    · exact hX X (Or.inr (Or.inr (Or.inl hT)))
  · obtain ⟨q, hq, hA | hB | hD⟩ := h8
    · exact evenLieType_of_isoLie_A hq hA
    · exact evenLieType_of_isoLie_B hq (by norm_num) hB
    · exact evenLieType_of_isoLie_twistedD hq hD
  · obtain ⟨q, hq, hf, hA4 | hA5 | hA6 | hU5 | hB4 | hD4 | hF4⟩ := h9
    · exact evenLieType_of_isoLie_A hq hA4
    · exact evenLieType_of_isoLie_A hq hA5
    · exact evenLieType_of_isoLie_A hq hA6
    · exact evenLieType_of_isoLie_twistedA hq hU5
    · exact evenLieType_of_isoLie_B hq (by norm_num) hB4
    · exact evenLieType_of_isoLie_D hq hD4
    · exact hX X (Or.inr (Or.inr (Or.inr ⟨q, hq, hf, hF4⟩)))

theorem item613_of_inspections' (hB : ThetaQuotientBookkeeping) (hT : ThmThreeCatalog)
    (hX : EvenExceptionalBridge) (h2 : Item613Item2) (h3 : Item613Item3) (h4 : Item613Item4)
    (h6 : Item613Item6) : Item613 :=
  item613_of_inspections hB hT (evenListBridge_of_exceptional hX) h2 h3 h4 h6

end CFSG.RankThree.PartOne.N143

module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityStatements
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Link
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Outer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Data

public section

open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartTwo.Sec4.Item434D42
open CFSG.AGLEmbedding.ChevOuter
open CFSG.RankThree.PartOne.Census3 (IsoLie)

namespace CFSG.RankThree.PartTwo.Sec19

@[expose] def TrialityTwoPlanes : Prop :=
  ∀ E : Subgroup (MulAut lineGroup), CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 →
    Subgroup.closure (fixUnion E) = ⊤

@[expose] def TrialityThreeInnerTwo : Prop :=
  ∀ q : TauCeti.PrimePower, q.p = 2 → q.exponent = 1 → ∀ (K : Type) [Group K] [Finite K]
    [IsSimpleGroup K], IsoLie K (.trialityD4 q) → ∀ E : Subgroup (MulAut K),
      CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 → (∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) →
        Subgroup.closure (fixUnion E) = ⊤

@[expose] def TrialityThreeOuterTwo : Prop :=
  ∀ q : TauCeti.PrimePower, q.p = 2 → q.exponent = 1 → ∀ (K : Type) [Group K] [Finite K]
    [IsSimpleGroup K], IsoLie K (.trialityD4 q) → ∀ E : Subgroup (MulAut K),
      CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 → ¬ (∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) →
        Subgroup.closure (fixUnion E) = ⊤

theorem closure_fixUnion_eq_top_of_equiv {K : Type*} [Group K] (e : K ≃* lineGroup)
    (h : TrialityTwoPlanes) {E : Subgroup (MulAut K)} (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) : Subgroup.closure (fixUnion E) = ⊤ := by
  have hE' : CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr e).toMonoidHom) :=
    isElementaryAbelian_of_isElemAbelian
      (isElemAbelian_map_congr e (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hE))
  have hcard' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 3 ^ 2 :=
    (card_map_congr e E).trans hcard
  have h1 := h _ hE' hcard'
  rw [← planeGen_iff_closure_fixUnion] at h1 ⊢
  exact planeGen_of_outer_model e h1

section KFacts

set_option linter.unusedSectionVars false


theorem lineGroup_facts_of_isoLie (q : TauCeti.PrimePower) (hq : q.p = 2) (hq1 : q.exponent = 1)
    {K : Type} [Group K] [Finite K] [IsSimpleGroup K] (h : IsoLie K (.trialityD4 q)) :
    Nonempty (K ≃* lineGroup) ∧ Subgroup.center lineGroup = ⊥ ∧
      Nat.card (MulAut lineGroup) = 3 * 211341312 := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  obtain ⟨hmod, ⟨eT⟩⟩ :=
    CFSG.AGLEmbedding.ChevOuter.exists_model_equiv ⟨.trialityD4 q, hv⟩ q hq hq1 rfl e
  refine ⟨⟨eT⟩, ?_⟩
  have hcardK : Nat.card K = 211341312 := by
    have hc := CFSG.AGLEmbedding.card_catGroup_trialityD4_even
      (d := ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩) hq rfl
    rw [Nat.card_congr e.toEquiv, hc, hq1]
    norm_num [CFSG.Open.ordTrialityD4]
  have hcardT : Nat.card lineGroup = 211341312 := by
    rw [← Nat.card_congr eT.toEquiv]
    exact hcardK
  haveI : IsSimpleGroup lineGroup := eT.symm.isSimpleGroup
  have hnab : ∃ a b : lineGroup, a * b ≠ b * a := by
    refine ⟨letterX 1, letterX 10, fun hab => ?_⟩
    have hm := congrArg (fun x : lineGroup => ((x : GL (Fin 8) CFSG.Quasithin.GF8) : Matrix (Fin 8) (Fin 8) CFSG.Quasithin.GF8))
      hab
    have hne : CFSG.AGLEmbedding.D4Two.letterMat 1 * CFSG.AGLEmbedding.D4Two.letterMat 10 ≠
        CFSG.AGLEmbedding.D4Two.letterMat 10 * CFSG.AGLEmbedding.D4Two.letterMat 1 := by
      decide +kernel
    exact hne (by simpa [letterX, CFSG.AGLEmbedding.D4Two.letterGL] using hm)
  have hZ : Subgroup.center lineGroup = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center lineGroup) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb' : b ∈ Subgroup.center lineGroup := ht ▸ Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.mp hb' a)
  refine ⟨hZ, ?_⟩
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer lineGroup) = 3 :=
    CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.card_outer_d42
      (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eT.symm hmod)
  have hinnCard : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner lineGroup) =
      Nat.card lineGroup := by
    show Nat.card (MulAut.conj : lineGroup →* MulAut lineGroup).range = _
    rw [← Nat.card_congr (MonoidHom.ofInjective
      (CFSG.RankThree.PartTwo.Sec4.Item434Kit.conj_injective_of_center_eq_bot hZ)).toEquiv]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner lineGroup), hinnCard, hcardT]
  have hOut' : Nat.card (MulAut lineGroup ⧸
      CFSG.ComponentClassification.OuterAutomorphisms.inner lineGroup) = 3 := hOut
  rw [hOut']

theorem trialityThreeInnerTwo_of_planes
    (hplanes : Subgroup.center lineGroup = ⊥ → Nat.card (MulAut lineGroup) = 3 * 211341312 →
      TrialityTwoPlanes) : TrialityThreeInnerTwo := by
  intro q hq hq1 K _ _ _ h E hE hcard _
  obtain ⟨⟨e⟩, hZ, hAut⟩ := lineGroup_facts_of_isoLie q hq hq1 h
  exact closure_fixUnion_eq_top_of_equiv e (hplanes hZ hAut) hE hcard

theorem trialityThreeOuterTwo_of_planes
    (hplanes : Subgroup.center lineGroup = ⊥ → Nat.card (MulAut lineGroup) = 3 * 211341312 →
      TrialityTwoPlanes) : TrialityThreeOuterTwo := by
  intro q hq hq1 K _ _ _ h E hE hcard _
  obtain ⟨⟨e⟩, hZ, hAut⟩ := lineGroup_facts_of_isoLie q hq hq1 h
  exact closure_fixUnion_eq_top_of_equiv e (hplanes hZ hAut) hE hcard

end KFacts

theorem trialityThreeInner_of_split (h1 : TrialityThreeInnerTwo)
    (h2 : ∀ q : TauCeti.PrimePower, q.p = 2 → 2 ≤ q.exponent → ∀ (K : Type) [Group K] [Finite K]
      [IsSimpleGroup K], IsoLie K (.trialityD4 q) → ∀ E : Subgroup (MulAut K),
        CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 → (∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) →
          Subgroup.closure (fixUnion E) = ⊤) :
    TrialityThreeInner := by
  intro q hq K _ _ _ h E hE hcard hin
  rcases Nat.lt_or_ge q.exponent 2 with hlt | hge
  · have hq1 : q.exponent = 1 := by have := q.exponent_pos; omega
    exact h1 q hq hq1 K h E hE hcard hin
  · exact h2 q hq hge K h E hE hcard hin

theorem trialityThreeOuter_of_split (h1 : TrialityThreeOuterTwo)
    (h2 : ∀ q : TauCeti.PrimePower, q.p = 2 → 2 ≤ q.exponent → ∀ (K : Type) [Group K] [Finite K]
      [IsSimpleGroup K], IsoLie K (.trialityD4 q) → ∀ E : Subgroup (MulAut K),
        CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 → ¬ (∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) →
          Subgroup.closure (fixUnion E) = ⊤) :
    TrialityThreeOuter := by
  intro q hq K _ _ _ h E hE hcard hout
  rcases Nat.lt_or_ge q.exponent 2 with hlt | hge
  · have hq1 : q.exponent = 1 := by have := q.exponent_pos; omega
    exact h1 q hq hq1 K h E hE hcard hout
  · exact h2 q hq hge K h E hE hcard hout

end CFSG.RankThree.PartTwo.Sec19

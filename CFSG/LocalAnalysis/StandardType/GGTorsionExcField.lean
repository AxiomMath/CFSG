module

public import CFSG.LocalAnalysis.StandardType.GGTorsionExcDefs
public import CFSG.LocalAnalysis.StandardType.GGCompFieldLieModel
public import CFSG.LocalAnalysis.StandardType.GGCompFieldCatalogue
public import CFSG.LocalAnalysis.StandardType.GGTorsionQuotComp
public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestE6
public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionExcField

private theorem txf_index_of_chevalley
    {G : Type} [Group G] {t : CFSG.Open.StatedLieTag} {p f : ℕ}
    (ht : t ∈ CFSG.Blueprint.chevalleyExceptionalTags)
    (h : CFSG.Blueprint.ChevalleyExceptionalModel G t p f) :
    ∃ d : TauCeti.ValidLieTypeIndex,
      d.1.characteristic = p ∧ ¬ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.suzRee d.1 ∧
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 = p ^ f ∧
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  obtain ⟨hadm, hm⟩ := h
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
  have hq : q.card = p ^ f := TauCeti.PrimePower.card_def q
  cases t <;> simp only [CFSG.Blueprint.chevalleyExceptionalTags, Finset.mem_insert,
    Finset.mem_singleton, reduceCtorEq, or_false, false_or] at ht
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
      refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
      · simpa [TauCeti.LieTypeIndex.inStandardRange_iff, hq] using hadm.2.2.2
      · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    obtain ⟨b⟩ := hB.g2 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, by simp [q], by simp [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.suzRee],
      by show q.card = p ^ f; rw [hq], ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (TauCeti.LieTypeIndex.F4 q).Valid := by simp
    obtain ⟨b⟩ := hB.f4 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, by simp [q], by simp [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.suzRee],
      by show q.card = p ^ f; rw [hq], ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (TauCeti.LieTypeIndex.E6 q).Valid := by simp
    obtain ⟨b⟩ := hB.e6 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, by simp [q], by simp [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.suzRee],
      by show q.card = p ^ f; rw [hq], ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (TauCeti.LieTypeIndex.E7 q).Valid := by simp
    obtain ⟨b⟩ := hB.e7 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, by simp [q], by simp [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.suzRee],
      by show q.card = p ^ f; rw [hq], ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (TauCeti.LieTypeIndex.E8 q).Valid := by simp
    obtain ⟨b⟩ := hB.e8 q hv K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, by simp [q], by simp [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.suzRee],
      by show q.card = p ^ f; rw [hq], ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid := by simp
    obtain ⟨b⟩ := hB.twistedE6 q hv K (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨⟨_, hv⟩, by simp [q], by simp [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.suzRee],
      by show q.card = p ^ f; rw [hq], ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid := by simp
    obtain ⟨b⟩ := hB.trialityD4 q hv K (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨⟨_, hv⟩, by simp [q], by simp [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.suzRee],
      by show q.card = p ^ f; rw [hq], ⟨e.trans b⟩⟩

private theorem txf_inndiagComm_labelAll
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hexc : GGTorsionAmbExc lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  rcases hexc with hE6 | hE7 | hE8 | hF4 | htwE6 | htriD4 | hG2
  · exact largeEvenLabelAll_inndiagComm_E6 hE6
  · exact largeEvenLabelAll_inndiagComm_proved hlab (by
      simp [GGInndiagCommProvedLabel, GGRecipeExcOutLabel, hE7])
  · exact largeEvenLabelAll_inndiagComm_proved hlab (by
      simp [GGInndiagCommProvedLabel, GGRecipeExcOutLabel, hE8])
  · exact largeEvenLabelAll_inndiagComm_proved hlab (by
      simp [GGInndiagCommProvedLabel, GGRecipeExcOutLabel, hF4])
  · exact largeEvenLabelAll_inndiagComm_twE6 hlab htwE6
  · exact largeEvenLabelAll_inndiagComm_triD4 hlab htriD4
  · exact largeEvenLabelAll_inndiagComm_proved hlab (by
      simp [GGInndiagCommProvedLabel, GGRecipeExcOutLabel, hG2])

private theorem txf_markTag_mem_chevalleyExceptional {lab : LargeEvenLabel}
    (hexc : GGTorsionAmbExc lab) : markTag lab ∈ CFSG.Blueprint.chevalleyExceptionalTags := by
  rcases hexc with h | h | h | h | h | h | h <;>
    simp [markTag, CFSG.Blueprint.chevalleyExceptionalTags, h]

private theorem txf_markChar_eq_two {lab : LargeEvenLabel} (hexc : GGTorsionAmbExc lab) :
    markChar lab = 2 := by
  rcases hexc with h | h | h | h | h | h | h <;> simp [markChar, h]

private theorem txf_markDeg_eq {lab : LargeEvenLabel} (hexc : GGTorsionAmbExc lab) :
    markDeg lab = lab.n := by
  rcases hexc with h | h | h | h | h | h | h <;> simp [markDeg, h]

private theorem txf_fieldData_of_equiv {X R : Type} [Group X] [Group R] {J : Subgroup X}
    {Jbar : Subgroup R} {q : ℕ}
    (e : ↥J ⧸ Subgroup.center ↥J ≃* ↥Jbar ⧸ Subgroup.center ↥Jbar)
    (h : GGCompFieldDataQ q Jbar) : GGCompFieldDataQ q J := by
  unfold GGCompFieldDataQ at h ⊢
  rcases h with ⟨m, hm, hat⟩ | ⟨h2, hcard⟩
  · left
    refine ⟨m, hm, ?_⟩
    unfold GGCompFieldAt at hat ⊢
    obtain ⟨lab, hlab, hchar, hdeg, h1, h2, h3, hhas, R', hgrp, hmm, hiso⟩ := hat
    refine ⟨lab, hlab, hchar, hdeg, h1, h2, h3, ?_, R', hgrp, hmm, ?_⟩
    · exact largeEvenRawDatum_mono (fun _ _ _ _ ⟨f⟩ => ⟨e.trans f⟩) hhas
    · obtain ⟨f⟩ := hiso
      exact ⟨e.trans f⟩
  · right
    refine ⟨h2, ?_⟩
    rw [Nat.card_congr e.toEquiv]
    exact hcard

theorem ggTorsion_exc_fieldData
    {P : LargeEvenLabel → Prop} (hP : ∀ lab, P lab → GGTorsionAmbExc lab)
    {p : ℕ} {X : Type} [Group X] {δ : MulAut X} {J : Subgroup X}
    (hdat : GGTorsionDatum P p δ J) :
    LargeEvenMarking X fun lab _ _ _ _ _ => P lab ∧ GGCompFieldDataQ (2 ^ lab.n) J := by
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  have hexc : GGTorsionAmbExc lab := by
    obtain ⟨_, _, _, _, _, _, _, hP0, -⟩ := largeEvenRawDatum_exists hraw
    exact hP lab hP0
  have hrawMM : LargeEvenRawDatumLegacy lab
      (fun R _ I _ => (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, P lab ∧ ggInducedAut θ δ ∈ I) ∧ MarkedModel lab R) :=
    largeEvenRawDatum_markedModel hlab
      (fun _ _ _ _ ⟨_, hna, _, _, _⟩ => hna) hraw
  have hraw' := (txf_inndiagComm_labelAll hlab hexc) _ hrawMM
  obtain ⟨R, _, I, F, ⟨⟨hs, hna, θ, _, hδI⟩, hm⟩, hGuard⟩ :=
    largeEvenRawDatum_exists hraw'
  have hEq : GGInndiagCommEq R I F := hGuard hs hna
  let δbar : MulAut R := ggInducedAut θ δ
  have hδbar1 : δbar ≠ 1 := by
    intro h
    apply hδ1
    exact ggInducedAut_injective_of_perfect hXc θ (h.trans (map_one _).symm)
  have hδbarp : δbar ^ p = 1 := by
    dsimp [δbar]
    rw [← map_pow, hδp, map_one]
  have hβ : δbar ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived R := by
    have hmem : δbar ∈ ggInndiag R I := Subgroup.mem_sup_right (Subgroup.subset_closure hδI)
    have hmem2 : δbar ∈ ggInndiagComm R := by rw [← hEq]; exact hmem
    rwa [ggInndiagComm_eq_innAutDerived] at hmem2
  let Jbar : Subgroup R :=
    J.map ((θ : X ⧸ Subgroup.center X →* R).comp (QuotientGroup.mk' (Subgroup.center X)))
  have hJbar : IsComponentOf Jbar (ggAutFixedSubgroup δbar) := by
    dsimp [Jbar, δbar]
    exact ggTorsion_isComponentOf_image θ hcomp
  have hC : CFSG.Open.IsComponentOf Jbar
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δbar) := by
    have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δbar =
        ggAutFixedSubgroup δbar := Subgroup.ext fun _ => Iff.rfl
    rw [hfix]
    exact isComponentOf_iff_open.mp hJbar
  have ht : markTag lab ∈ CFSG.Blueprint.chevalleyExceptionalTags :=
    txf_markTag_mem_chevalleyExceptional hexc
  have hchev : CFSG.Blueprint.ChevalleyExceptionalModel R (markTag lab) 2 lab.n := by
    have hm0 : CFSG.Blueprint.LieModel R (markTag lab) (markRank lab) (markChar lab)
        (markDeg lab) := hm
    have h := hm0.chevalleyExceptionalModel ht
    rw [txf_markChar_eq_two hexc, txf_markDeg_eq hexc] at h
    exact h
  obtain ⟨d, hd, hdsr, hk, he⟩ := txf_index_of_chevalley ht hchev
  obtain ⟨e⟩ := he
  have hpq : p ≠ d.1.characteristic := by rw [hd]; exact hp2
  have hIcomp : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.CompIdxAt p d.1
      (TauCeti.CFSGIndex.lie d).Group :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.lieCompIdx_all d p hp hp2 hpq trivial
  have hIcomp' : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.CompIdxAt p d.1 R :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.compIdxAt_of_mulEquiv e.symm hIcomp
  obtain ⟨i, ⟨φ⟩, hrel⟩ := hIcomp' δbar hβ hδbarp hδbar1 Jbar hC
  have hq : CFSG.Open.IsQuasisimple ↥Jbar := hC.2.2
  have hfdJbar : GGCompFieldDataQ (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1) Jbar :=
    ggCompFieldDataQ_of_compRelC hq hd hdsr hk hrel φ
  obtain ⟨eJ⟩ := ggTorsion_centerQuot_image_equiv θ hcomp.2.2.1
  have hfd : GGCompFieldDataQ (2 ^ lab.n) J := by
    rw [hk] at hfdJbar
    exact txf_fieldData_of_equiv eJ hfdJbar
  refine ⟨hXc, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R' _ I' F' ⟨hs', hna', θ', hPlab', _⟩
  exact ⟨hs', hna', θ', hPlab', hfd⟩

end TorsionExcField

end CFSG.StandardType

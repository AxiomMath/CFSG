module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentCited
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupTits
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupMcL
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZGeneric
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.LinTwo
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieNonUnitaryLin
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentIrred
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10
import CFSG.GroupTheory.PGroupPowTransfer
public import CFSG.CharacterTheory.Semidihedral.ActualLayerOddExtensions

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R78Five

open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)

private abbrev FirstRow (X : Type) [Group X] [Finite X] : Prop :=
  (∀ P : Sylow 5 X, (P : Subgroup X) ≤ CFSG.generalizedFitting X ∧
      ∀ x ∈ (P : Subgroup X), x ^ 5 = 1) ∧
    ∀ S : Sylow 5 ↥(CFSG.generalizedFitting X),
      CFSG.LocalAnalysis.RankThreeTheoremC.NormIrredFrattini
        (S : Subgroup ↥(CFSG.generalizedFitting X))

private theorem psl2GF_sylow_facts {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n)
    {K : Type} [Group K] [Finite K] (e : K ≃* CFSG.AGLEmbedding.PSL2GF p n)
    (S : Sylow p K) :
    (∀ x ∈ (S : Subgroup K), x ^ p = 1) ∧
      CFSG.LocalAnalysis.RankThreeTheoremC.NormIrredFrattini (S : Subgroup K) := by
  refine ⟨CFSG.GroupTheory.forall_pow_eq_one_sylow_of_mulEquiv e
    (fun T => (CFSG.AGLEmbedding.psl2GF_sylow p n hn T).1.2) S, ?_⟩
  exact (CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.Irred.irredAt_of_normIrred (p := p)
    (CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.Irred.normIrr_sylow_of_equiv e
      (fun T V hVT hV hVN =>
        CFSG.AGLEmbedding.KFactProofs.NonUnitary.psl2GF_invariant' hp2 hn T V hVT hV hVN)
      S)).1

private theorem firstRow {X : Type} [Group X] [Finite X]
    (hle : ∀ P : Sylow 5 X, (P : Subgroup X) ≤ CFSG.generalizedFitting X)
    (hexp : ∀ S : Sylow 5 ↥(CFSG.generalizedFitting X),
      ∀ x ∈ (S : Subgroup ↥(CFSG.generalizedFitting X)), x ^ 5 = 1)
    (hirr : ∀ S : Sylow 5 ↥(CFSG.generalizedFitting X),
      CFSG.LocalAnalysis.RankThreeTheoremC.NormIrredFrattini
        (S : Subgroup ↥(CFSG.generalizedFitting X))) : FirstRow X := by
  refine ⟨fun P => ⟨hle P, ?_⟩, hirr⟩
  intro x hx
  have hxS : (⟨x, hle P hx⟩ : ↥(CFSG.generalizedFitting X)) ∈
      (P.subtype (hle P) : Subgroup ↥(CFSG.generalizedFitting X)) := by
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
    exact hx
  have h := hexp (P.subtype (hle P)) ⟨x, hle P hx⟩ hxS
  simpa using congrArg Subtype.val h

private theorem firstRow_of_linTwo {X : Type} [Group X] [Finite X] {N : Subgroup X} {n : ℕ}
    (hn : 1 ≤ n) (hO : CFSG.pPrimeCore 5 X = ⊥)
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.PSL2GF 5 n) : FirstRow X :=
  firstRow
    (fun P => CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZ.le_of_forall_pElement_mem
      hN (fun z hz hzp =>
        (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.pElements_psl2GF
          (by norm_num) hn hO hN e).2 z hz hzp) P)
    (fun S => (psl2GF_sylow_facts (by norm_num) hn e S).1)
    (fun S => (psl2GF_sylow_facts (by norm_num) hn e S).2)

private theorem firstRow_of_unitary {X : Type} [Group X] [Finite X] {N : Subgroup X}
    {d : TauCeti.ValidLieTypeIndex} (hU : CFSG.AGLEmbedding.IsUnitaryIndex 5 d)
    (hstep : CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.StepThreeGroup 5
      ↥(CFSG.generalizedFitting X))
    (hIrr : CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.KFactStepThreeIrred)
    (hO : CFSG.pPrimeCore 5 X = ⊥)
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d) : FirstRow X :=
  firstRow
    (fun P => CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZ.le_of_forall_pElement_mem
      hN (fun z hz hzp =>
        (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.pElements_unitary
          hU hO hN e).2 z hz hzp) P)
    (fun S => (CFSG.AGLEmbedding.kFactUnitarySylowStructure ↥(CFSG.generalizedFitting X) 5 d
      (by norm_num) hU ⟨e⟩ S).2.2.1)
    (fun S => (hIrr 5 ↥(CFSG.generalizedFitting X) hstep S).1)

private theorem firstRow_of_altTen {X : Type} [Group X] [Finite X]
    (hIrr : CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.KFactStepThreeIrred)
    (hKC : Subgroup.centralizer (((CFSG.generalizedFitting X : Subgroup X) : Set X)) = ⊥)
    (e : ↥(CFSG.generalizedFitting X) ≃* alternatingGroup (Fin 10)) : FirstRow X := by
  have htype : CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.IsA10Type 5
      ↥(CFSG.generalizedFitting X) := ⟨rfl, ⟨e⟩⟩
  have hstep : CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.StepThreeGroup 5
      ↥(CFSG.generalizedFitting X) := by
    refine ⟨.alternating 10 (by norm_num), Or.inr ⟨rfl, rfl⟩, ?_⟩
    exact ⟨e⟩
  have hout : ¬ 5 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥(CFSG.generalizedFitting X)) := fun h =>
    (by norm_num : ¬ (5 : ℕ) ∣ 2) (h.trans
      (outer_card_dvd_two_of_equiv_outside_six (n := 10) (Or.inr (by norm_num)) e))
  exact firstRow
    (fun P => CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZ.le_of_not_dvd_card_outer
      hKC hout P)
    (fun S => (CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.a10_sylow _ htype S).1.2)
    (fun S => (hIrr 5 ↥(CFSG.generalizedFitting X) hstep S).1)

private theorem firstRow_of_tits {X : Type} [Group X] [Finite X]
    (hT : CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TitsFacts)
    (hIrr : CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.KFactStepThreeIrred)
    (hKC : Subgroup.centralizer (((CFSG.generalizedFitting X : Subgroup X) : Set X)) = ⊥)
    (htype : CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.IsTitsType 5
      ↥(CFSG.generalizedFitting X))
    (hstep : CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.StepThreeGroup 5
      ↥(CFSG.generalizedFitting X)) : FirstRow X :=
  firstRow
    (fun P => CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZ.le_of_not_dvd_card_outer
      hKC (hT.noOuter _ htype) P)
    (fun S => (hT.sylow _ htype S).1.2)
    (fun S => (hIrr 5 ↥(CFSG.generalizedFitting X) hstep S).1)

private theorem firstRow_of_mcL {X : Type} [Group X] [Finite X]
    (hM : CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLFacts)
    (hIrr : CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.KFactStepThreeIrred)
    (hKC : Subgroup.centralizer (((CFSG.generalizedFitting X : Subgroup X) : Set X)) = ⊥)
    (htype : CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.IsMcLType 5
      ↥(CFSG.generalizedFitting X))
    (hstep : CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.StepThreeGroup 5
      ↥(CFSG.generalizedFitting X)) : FirstRow X :=
  firstRow
    (fun P => CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZ.le_of_not_dvd_card_outer
      hKC (hM.noOuter _ htype) P)
    (fun S => (hM.sylow _ htype S).2.2)
    (fun S => (hIrr 5 ↥(CFSG.generalizedFitting X) hstep S).1)

theorem quotient_rows (hId : CFSG.AGLEmbedding.KFactSmallIdent)
    (hLie : CFSG.AGLEmbedding.KFactOneLieIdent)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hIrr : CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.KFactStepThreeIrred)
    (hT : CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TitsFacts)
    (hM : CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLFacts)
    {p : ℕ} (hp5 : p = 5) {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X)
    (hO : CFSG.pPrimeCore p X = ⊥) (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X))
    {N : Subgroup X} (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N) :
    ((∀ P : Sylow p X, (P : Subgroup X) ≤ CFSG.generalizedFitting X ∧
        ∀ x ∈ (P : Subgroup X), x ^ p = 1) ∧
      ∀ S : Sylow p ↥(CFSG.generalizedFitting X),
        CFSG.LocalAnalysis.RankThreeTheoremC.NormIrredFrattini
          (S : Subgroup ↥(CFSG.generalizedFitting X))) ∨
    CFSG.RankThree.PartOne.Census3.IsoLie ↥(CFSG.generalizedFitting X) (.suzuki 2) ∨
    CFSG.AGLEmbedding.IsFi22 ↥(CFSG.generalizedFitting X) ∨
    ∃ d : TauCeti.ValidLieTypeIndex, CFSG.AGLEmbedding.IsUnitaryIndex p d ∧
      2 ≤ d.1.fieldExponent ∧
      Nonempty (↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d) := by
  subst hp5
  classical
  obtain ⟨-, -, -, hKC⟩ :=
    CFSG.RankThree.PartOne.Sec1511.spe_fstar (p := 5) (by norm_num) hO hN
  rcases CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.identification_of_isStronglyPEmbedded
    hId hLie hCyc (by norm_num) (le_refl 5) hX hO h2 hN with hsmall | hlie | hsz
  ·
    unfold CFSG.AGLEmbedding.IsSmallStrongP at hsmall
    rcases hsmall with hlin | huni | halt | hthree | hfive | hj4
    ·
      unfold CFSG.AGLEmbedding.IsSmallLinTwo at hlin
      obtain ⟨d, hd, ⟨e₀⟩⟩ := hlin
      obtain ⟨e₁⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (n := 2) hd
      exact Or.inl (firstRow_of_linTwo (by norm_num) hO hN (e₀.trans e₁))
    ·
      unfold CFSG.AGLEmbedding.IsSmallUnitary at huni
      obtain ⟨d, ⟨q, hqp, hqx, hdq⟩, ⟨e⟩⟩ := huni
      have hU : CFSG.AGLEmbedding.IsUnitaryIndex 5 d := ⟨q, hqp, hdq⟩
      have hstep : CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.StepThreeGroup 5
          ↥(CFSG.generalizedFitting X) :=
        ⟨.lie d, Or.inr ⟨rfl, Or.inr (Or.inl ⟨q, hqp, hqx, hdq⟩)⟩, ⟨e⟩⟩
      exact Or.inl (firstRow_of_unitary hU hstep hIrr hO hN e)
    ·
      unfold CFSG.AGLEmbedding.IsAltTwoP at halt
      obtain ⟨e⟩ := halt
      have e10 : ↥(CFSG.generalizedFitting X) ≃* alternatingGroup (Fin 10) := e
      exact Or.inl (firstRow_of_altTen hIrr hKC e10)
    ·
      obtain ⟨h3, -⟩ := hthree
      omega
    ·
      obtain ⟨-, hTits | hMc | hFi22⟩ := hfive
      ·
        obtain ⟨⟨d₀, hv⟩, hd, ⟨e⟩⟩ := hTits
        obtain rfl : d₀ = .tits := hd
        have htype : CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.IsTitsType 5
            ↥(CFSG.generalizedFitting X) := ⟨rfl, ⟨hv, ⟨e⟩⟩⟩
        have hstep : CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.StepThreeGroup 5
            ↥(CFSG.generalizedFitting X) :=
          ⟨.lie ⟨.tits, hv⟩, Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr rfl))⟩, ⟨e⟩⟩
        exact Or.inl (firstRow_of_tits hT hIrr hKC htype hstep)
      ·
        obtain ⟨e⟩ := hMc
        have htype : CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.IsMcLType 5
            ↥(CFSG.generalizedFitting X) := ⟨rfl, ⟨e⟩⟩
        have hstep : CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.StepThreeGroup 5
            ↥(CFSG.generalizedFitting X) :=
          ⟨.sporadic .McL, Or.inr ⟨rfl, rfl⟩, ⟨e⟩⟩
        exact Or.inl (firstRow_of_mcL hM hIrr hKC htype hstep)
      ·
        exact Or.inr (Or.inr (Or.inl hFi22))
    ·
      obtain ⟨h11, -⟩ := hj4
      omega
  ·
    obtain ⟨d, hcases, ⟨e⟩⟩ := hlie
    rcases hcases with ⟨n, hn3, hd⟩ | ⟨hU, hfe⟩ | hree
    ·
      obtain ⟨e₁⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
      exact Or.inl (firstRow_of_linTwo (by omega) hO hN (e.trans e₁))
    ·
      exact Or.inr (Or.inr (Or.inr ⟨d, hU, hfe, ⟨e⟩⟩))
    ·
      obtain ⟨h3, -⟩ := hree
      omega
  ·
    exact Or.inr (Or.inl hsz.2)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R78Five

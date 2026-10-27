module

public import CFSG.StandardComponent.AschbacherSeitz.A5Child
public import CFSG.StandardComponent.AschbacherSeitz.SpConversions
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenFive
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.GMS78GapHKSAffineProof
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4HomoResT0
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4RootCore
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.RankTwoClassical
open CFSG.ComponentClassification.RankTwoAltFive
open CFSG.ComponentClassification.RankTwoAlt
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.Asc76X
open CFSG.ComponentClassification.GMS78
open scoped MatrixGroups

section Certified

theorem spTwo_small_case (G : Type) [Group G] [Finite G] (A : Subgroup G) (f : ℕ)
    (hstd : standardComponentIsStandard A) (hO : standardComponentOddCore G = ⊥)
    (hrank : 2 ≤ CFSG.Open.pRank 2 (Subgroup.centralizer (A : Set G)))
    (hAsp : Nonempty (A ≃* StatedSp 1 (GaloisField 2 f))) (hf : 2 ≤ f) :
    Subgroup.normalClosure (A : Set G) = A ∨
      (f = 2 ∧
        (Nonempty (Subgroup.normalClosure (A : Set G) ≃* alternatingGroup (Fin 9)) ∨
          NativeSporadic.IsSporadic (Subgroup.normalClosure (A : Set G)) .M12 ∨
          NativeSporadic.IsSporadic (Subgroup.normalClosure (A : Set G)) .J2)) := by
  by_cases hN : A.Normal
  · haveI : A.Normal := hN
    exact Or.inl (Subgroup.normalClosure_eq_self A)
  · by_cases hf2 : f = 2
    · subst hf2
      obtain ⟨e⟩ := hAsp
      have hA5 : Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin 5)) :=
        spTwoFourQuotEquivA5 e
      have hH : RankTwoHypNF G A := ⟨hstd, hN, hrank⟩
      have h32 := CFSG.ComponentClassification.RankTwoFoundation.lemma32
      have h332 := CFSG.ComponentClassification.RankTwoFoundation.lemma33Two
      have h4 := CFSG.ComponentClassification.RankTwoFoundation.asc75Theorem4
      have h34 := asc08Lemma34
      have hcfg := CFSG.ComponentClassification.RankTwoFoundation.section3Config
      have hGen5 := altGenerationFive_of asc08Lemma34
        goldschmidtTheoremA
      have hI := altFiveCaseINF_of_lemmas h32 h332 hGen5
      have hIIa := asc310IIa_of'
        (asc310EpsOne_of goldschmidtTheoremA)
      have hIIb := asc310IIb
      have hM12 := altFiveM12NotTopNF
      have hEven := altEvenCenterSmallNF_of h32 h4 h34 hcfg
      have hchild := altChildAt_fiveNF h32 h332 hcfg hI hIIa hIIb hM12 hEven
      rcases hchild G A hH hO hA5 with h9 | ⟨-, hJ⟩ | ⟨-, hM, -⟩
      · exact Or.inr ⟨rfl, Or.inl h9⟩
      · exact Or.inr ⟨rfl, Or.inr (Or.inr hJ)⟩
      · exact Or.inr ⟨rfl, Or.inr (Or.inl hM)⟩
    · have hf3 : 3 ≤ f := by omega
      obtain ⟨e⟩ := hAsp
      have hPSL : Nonempty (rankTwoQuot A ≃* PSL(2, GaloisField 2 f)) :=
        spTwoQuotEquivPSL (f := f) (by omega) e
      obtain ⟨ePSL⟩ := hPSL
      have hmodel : StatedClassicalModel (rankTwoQuot A) .PSL 2 2 f :=
        stated_psl2_of_mulEquiv hf3 ePSL
      have hB : BenderHyp G A :=
        ⟨hstd, hO, hN, hrank, Or.inl ⟨f, hf3, hmodel⟩⟩
      have hF : Foundation :=
        ⟨CFSG.ComponentClassification.RankTwoFoundation.lemma32, CFSG.ComponentClassification.RankTwoFoundation.lemma33One,
          CFSG.ComponentClassification.RankTwoFoundation.lemma33Two, CFSG.ComponentClassification.RankTwoFoundation.lemma33Three,
          CFSG.ComponentClassification.RankTwoFoundation.asc75Theorem4⟩
      have hL2 := l2Res_of_gms42ResidualU hF hksRegularNormalAffine
        (gms42ResidualU_of gms42ResidualT0 gms42ResidualRoot)
      exact (hL2 G A hB f hf3 ⟨ePSL⟩).elim

end Certified

end CFSG.RankThree.GF2n.Tim79a

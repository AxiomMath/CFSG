module

public import CFSG.RankThree.GF2n.Tim79aCitedAS
public import CFSG.StandardComponent.AschbacherSeitz.SpClassical
public import CFSG.StandardComponent.AschbacherSeitz.SpSmall
public import CFSG.StandardComponent.AschbacherSeitz.SpConversions
public import CFSG.StandardComponent.AschbacherSeitz.Sp44EndgameNF

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.RankTwoClassical
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoAltFive
open CFSG.ComponentClassification.RankTwoAlt
open CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.Asc76X
open CFSG.Quasithin.SteinbergCB
open scoped MatrixGroups

section Certified

theorem asc08Lemma310LocalNF_holds : Asc08Lemma310LocalNF :=
  asc08Lemma310LocalNF_of_cases
    (asc310IIa_of' (asc310EpsOne_of goldschmidtTheoremA)) asc310IIb

theorem asc08Lemma310NF_holds :
    Asc08Lemma310NF :=
  asc08Lemma310NF_of_local asc08Lemma310LocalNF_holds
    CFSG.ComponentClassification.RankTwoFoundation.lemma32
    CFSG.ComponentClassification.RankTwoFoundation.lemma33Two
    CFSG.ComponentClassification.RankTwoFoundation.section3Config

theorem aschbacherSeitzStatement_holds : AschbacherSeitzStatement := by
  intro G _ _ A m f hm hf hAsp hO hstd hrank
  by_cases hN : A.Normal
  · haveI : A.Normal := hN
    exact Or.inl (Subgroup.normalClosure_eq_self A)
  · rcases (by omega : m = 1 ∨ 2 ≤ m) with hm1 | hm2
    · subst hm1
      rcases spTwo_small_case G A f hstd hO hrank hAsp hf with hnorm | ⟨hf2, hout⟩
      · exact Or.inl hnorm
      · exact Or.inr ⟨rfl, hf2, hout⟩
    · obtain ⟨e⟩ := hAsp
      have hpow : (m, 2 ^ f) ≠ (2, 2) := by
        intro h
        have h2 : 2 ^ f = 2 := congrArg Prod.snd h
        have h4 : 4 ≤ 2 ^ f := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
        omega
      have htype : SpClassicalType (rankTwoQuot A) := by
        refine ⟨m, f, hm2, hf, ?_⟩
        refine ⟨⟨Nat.prime_two, by omega, hm2, hpow⟩,
          ⟨GaloisField 2 f, inferInstance, inferInstance,
            GaloisField.card 2 f (by omega), ?_⟩⟩
        exact spQuotEquivProj (n := m) (K := GaloisField 2 f) (by omega) e
      have h32 := CFSG.ComponentClassification.RankTwoFoundation.lemma32
      have h332 := CFSG.ComponentClassification.RankTwoFoundation.lemma33Two
      have hcfg := CFSG.ComponentClassification.RankTwoFoundation.section3Config
      have h5 := asc08Lemma310NF_of_local
        (asc08Lemma310LocalNF_of_cases
          (asc310IIa_of' (asc310EpsOne_of goldschmidtTheoremA)) asc310IIb) h32 h332 hcfg
      have hSp44 : Sp44Step := sp44Step_of (sp44EndgameNF_of h32 h5
        CFSG.ComponentClassification.RankTwoClassical.J2Std.j2A4Facts m12AutThreeFive)
      have hnormal := spClassicalNormal_of_sp44 hSp44
      exact absurd (hnormal G A hstd hO hrank htype) hN

end Certified

end CFSG.RankThree.GF2n.Tim79a

module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Assemble
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Arith
public import CFSG.Quasithin.EmptyFaithful.A38c18Field
public import CFSG.Quasithin.EmptyFaithful.S1421STFinal2
public import CFSG.Quasithin.EmptyFaithful.S1421QWire
public import CFSG.Quasithin.EmptyFaithful.S1421QWire2
public import CFSG.Quasithin.EmptyFaithful.S1421QA12Main
public import CFSG.Quasithin.EmptyFaithful.S1421QD4Bridge
public import CFSG.Quasithin.EmptyFaithful.S1421QA13bMain
public import CFSG.Quasithin.EmptyFaithful.S1421QA13aMain
public import CFSG.Quasithin.EmptyFaithful.S1421QA25Main
public import CFSG.Quasithin.EmptyFaithful.S1421QA25M23
public import CFSG.Quasithin.EmptyFaithful.S1421QA28Top
public import CFSG.Quasithin.EmptyFaithful.S1421QA15Main
public import CFSG.Quasithin.EmptyFaithful.S1421QA19Main
public import CFSG.Quasithin.EmptyFaithful.S1421QA20Main
public import CFSG.Quasithin.EmptyFaithful.S1421QA21Main
public import CFSG.Quasithin.EmptyFaithful.S1421QA22Wire
public import CFSG.Quasithin.EmptyFaithful.S1421QA22L3
public import CFSG.Quasithin.EmptyFaithful.S1421QA22Mathieu
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115ListProved
public import CFSG.Quasithin.Vol2.Ch11SecAKE8
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Emb
public import CFSG.Quasithin.EmptyFaithful.S1421QA23Sporadic
public import CFSG.Quasithin.EmptyFaithful.S1421QA24Main
public import CFSG.Quasithin.EmptyFaithful.S1421QA26Top
public import CFSG.Quasithin.Vol2.Ch1EightTwoHubs
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4FinalHolds
public import CFSG.Quasithin.EmptyFaithful.SzSurvLocStmt
public import CFSG.Quasithin.EmptyFaithful.SzSurvLocQ1
public import CFSG.Quasithin.EmptyFaithful.SzSurvLocQ2
public import CFSG.Quasithin.EmptyFaithful.SzSurvLocJ2
public import CFSG.Quasithin.EmptyFaithful.SzSurvLocZSNSet

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.GoldS146R

namespace SzSurvLoc

theorem lemma_14_2_16_survivorLoc_of_R1PlusLoc {G : Type} [Group G] [Finite G]
    {T M H K1 : Subgroup G} (hR1 : F112R1PlusLocStatement)
    (h209 : Lemma14209Used) (h311 : Theorem311) (st : Setting1427 T M H K1)
    (h13 : pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1)
    (hf : CharTwo (S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 ⊔
      borelOf K1 (S1421.sOf T K1)))
    (h15 : pCoreOf 2 (K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1) = ⊥)
    (hbridge : ∀ (X : Type) [Group X], Nonempty (X ≃* Equiv.Perm (Fin 3)) → IsL2Quot 1 X) :
    F112SurvivorLoc K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) :=
  hR1 G K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) (quasithinOmegaOneCenter T)
    (S1421.r1Setting_of_setting1427_legacyBare h311 st h13 hf h15 hbridge)
    (hZS_of_nonab_setting1427 h209 h311 st h13 hf h15) st.notation_.bender

end SzSurvLoc

namespace F146Field

theorem stageTheorem1427Field_of_R1PlusLoc (hFacts : Facts1422Input)
    (hBig : E22InputBig) (h311 : Theorem311) (h13 : Lemma14213) (hf : Hyp111fInput)
    (h15 : Lemma14215)
    (hR1 : F112R1PlusLocStatement) (h209 : Lemma14209Used) (htail : Lemma14216TailLoc)
    (h17 : Lemma14217J2Loc) (h18 : Lemma14218D4LegacyBare) (hI47 : I47Statement) (hF431 : F431D4)
    (hD4 : TrialityD4Bridge) : A38c18.StageTheorem1427Field := by
  intro G _ _ T M hyp
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨H, K₂, hH, hns, hK₂, hHK₂, hcases, n, hn, hn1⟩, hnotB⟩ := hcon
  have F := hFacts G T M hyp
  have hn2 : 2 ≤ n := by
    have := hn.one_le
    omega
  have hmin : MinParabolic H T (H ⊓ M) := hyp.minParabolic hH
  have hsqtk : SQTKGroup ↥H :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot hyp.qtke hH.1.2,
      kGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hH.1.2⟩
  obtain ⟨K1, N, sh⟩ := hBig G T M H K₂ hH hmin hsqtk hK₂ hHK₂
    (e22CasesBig_of_field arithAll hn2 hn hcases)
  have st : Setting1427 T M H K1 := ⟨hyp, F, hH, N, sh⟩
  have h13' : pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 := by
    by_cases hO : pCoreOf 2 M ≤ S1421.sOf T K1
    · exact S1421.lemma_14_2_13_of_pCore_le hO
    · exact h13 G T M H K1 st hO
  have hf' : CharTwo (S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 ⊔
      borelOf K1 (S1421.sOf T K1)) := by
    by_cases hO : pCoreOf 2 M ≤ S1421.sOf T K1
    · exact S1421.hyp111f_of_pCore_le st hO
    · exact hf G T M H K1 st hO h13'
  have h15' : pCoreOf 2 (K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1) = ⊥ := by
    by_cases hS : S1421.sOf T K1 = T
    · exact S1421.lemma_14_2_15_of_sOf_eq st hS
    · exact h15 G T M H K1 st (lt_of_le_of_ne S1421.sOf_le_T hS) h13'
  have hsurv := SzSurvLoc.lemma_14_2_16_survivorLoc_of_R1PlusLoc hR1 h209 h311 st h13' hf' h15'
    (fun _ _ h => isL2Quot_one_iff_perm3.mpr h)
  have htl := htail G T M H K1 st h13' hsurv
  rcases hsurv with h4 | h10 | h11
  · obtain ⟨M₁, M₂, z, hext, hz2, hz1, hzr, hzc, hzC⟩ := h18 G T M H K1 st h13' h4 htl
    obtain ⟨D, _, hD, ⟨e⟩⟩ :=
      hF431 G hyp.simple hyp.nonabelian M₁ M₂ z hext hz2 hz1 hzr hzc hzC
    obtain ⟨e'⟩ := hD4 D hD
    exact hnotB.1.false (e.trans e')
  · obtain ⟨z, hz2, hz1, hC, hQ, hA, hw, hcnt⟩ := h17 G T M H K1 st h13' (Or.inl h10) htl
    obtain ⟨hJ2, hJ3⟩ := hI47 G hyp.simple hyp.nonabelian z hz2 hz1 hC hQ hA hw
    rcases hcnt with h1 | h2
    · exact hnotB.2.2.false (hJ3 h1).some
    · exact hnotB.2.1.false (hJ2 h2).some
  · obtain ⟨z, hz2, hz1, hC, hQ, hA, hw, hcnt⟩ := h17 G T M H K1 st h13' (Or.inr h11) htl
    obtain ⟨hJ2, hJ3⟩ := hI47 G hyp.simple hyp.nonabelian z hz2 hz1 hC hQ hA hw
    rcases hcnt with h1 | h2
    · exact hnotB.2.2.false (hJ3 h1).some
    · exact hnotB.2.1.false (hJ2 h2).some

theorem stageTheorem1427Field_of_stages₃_R1PlusLoc
    (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hBig : E22InputBig) (h311 : Theorem311) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h12 : Lemma14212) (hF : L34F98Impossible) (hN : L34NonabelianO2Y)
    (h209 : Lemma14209Used) (h3 : Lemma14215Core3) (hQ : Lemma14216QLoc)
    (hR1 : F112R1PlusLocStatement) (h17 : Lemma14217J2Loc)
    (h18 : Lemma14218D4LegacyBare) (hI47 : I47Statement) (hF431 : F431D4) (hD4 : TrialityD4Bridge) :
    A38c18.StageTheorem1427Field :=
  stageTheorem1427Field_of_R1PlusLoc (facts1422Input_of_stages h11 h113) hBig h311
    (lemma14213_of_inputs h12 hF hN) (hyp111fInput_of_lemma14212 h12)
    (lemma14215_of_14209_core3 h37 h38 h39 h209 h3) hR1 h209
    (lemma14216TailLoc_of_parts hQ) h17 h18 hI47 hF431 hD4

end F146Field

namespace SzPS8

section Stages

theorem stageTheorem1427Field_of_stages₄_R1PlusLoc (h38c : Vol2Native.A38ForSQTKCat)
    (h11 : StageLemma14111) (h113 : StageLemma14113) (h311 : Theorem311) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h12 : Lemma14212) (hF : L34F98Impossible)
    (hN : L34NonabelianO2Y) (h209 : Lemma14209Used) (h3 : Lemma14215Core3) (hQ : Lemma14216QLoc)
    (hR1 : F112R1PlusLocStatement)
    (h17 : Lemma14217J2Loc) (h18 : Lemma14218D4LegacyBare) (hI47 : I47Statement) (hF431 : F431D4)
    (hD4 : TrialityD4Bridge) : A38c18.StageTheorem1427Field :=
  F146Field.stageTheorem1427Field_of_stages₃_R1PlusLoc h11 h113 (F146Field.e22InputBig h38c) h311
    h37 h38 h39 h12 hF hN h209 h3 hQ hR1 h17 h18 hI47 hF431 hD4

end Stages

theorem stageTheorem1427Field_of_leaves_R1PlusLoc
    (h38c : Vol2Native.A38ForSQTKCat) (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h311 : Theorem311) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (hF318 : A318Facts)
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G)
    (hSL2 : A312SL2Fact) (h56 : AsB56) (hcover : AsA36NoOddCover) (hG2c : FactG2Cayley)
    (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hB45 : AsB45) (hD310 : D310)
    (hRigid : D4AmalgamRigid) (hI47 : I47Statement) (hR1 : F112R1PlusLocStatement) :
    A38c18.StageTheorem1427Field := by
  have h128One : Lemma128One := H13.NQCat.lemma128One_holds
  have h128Two : Lemma128Two := Ch1Two.lemma128Two_of h312
  have h128Four : Lemma128Four := Ch1Four.lemma128Four_of h312
  have hL34 : Q9.L34Maximal := Q9.l34Maximal_of_diagram h312 QA25.m23L34Diagram_holds
  have h209 : Lemma14209Used :=
    lemma14209Used_holds h37 h38 h39 h128One h128Two h128Four hL34
  exact stageTheorem1427Field_of_stages₄_R1PlusLoc h38c h11 h113 h311 h37 h38 h39
    (lemma14212_of_three_holds (lemma14212Three_of_inputs h37 h38 h39 h128Four hL34))
    (l34F98Impossible_of_inputs hA21 hG2c hB42 hB45 hD310) QA13a.l34NonabelianO2Y h209
    (lemma14215Core3_of_inputs h129
        (core3QuasiList_of_inputs H13.factMathieuOrders_holds Vol2.Ch11.SecA.factL2Parabolic_holds
            h36 h312 h37 QuasithinUnique.Ch1.lemma115_3_List_proved lemma115OrdClass_holds
            l3InvCentSolvable_holds m22InvFiveFree_holds m23InvFiveFree_holds)
        (core3QuasiBig_of_parts hF318 h36 h38 core3BigExclusion_holds core3BigParabolic_holds)
        (core3QuasiSmall_of_inputs hF318 h36 h37 h38 h39 (lemma14215Step2_of_14209 h37 h38 h39 h209) h209 h128Four hL34).1
        (core3QuasiSmall_of_inputs hF318 h36 h37 h38 h39 (lemma14215Step2_of_14209 h37 h38 h39 h209) h209 h128Four hL34).2
        (core3HeOdd_of_inputs h129 h36 h37 hSL2)
        (core3HeSyl_of_inputs_a7 h56 hcover hG2c (lemma14210_of_14209 h37 h38 h39 h209) h209
            QA23.factSporadicOrders H13.factMathieuOrders_holds Vol2.Ch11.SecA.factL2Parabolic_holds
            h36 h312 h37))
    lemma14216QLoc_holds hR1 lemma14217J2Loc_holds
    (S1421QA18.lemma14218D4_of_inputs_legacyBare h311 (QA28.lemma14218Normal_of_a312_legacyBare h312 h37 h38 h39)
      hRigid d4Order_holds)
    hI47 D4Hex.f431D4_holds trialityD4Bridge_holds

end SzPS8

theorem fieldOne146_of_leaves_R1PlusLoc
    (h38c : Vol2Native.A38ForSQTKCat) (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h311 : Theorem311) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (hF318 : A318Facts)
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G)
    (hSL2 : A312SL2Fact) (h56 : AsB56) (hcover : AsA36NoOddCover) (hG2c : FactG2Cayley)
    (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hB45 : AsB45) (hD310 : D310)
    (hRigid : D4AmalgamRigid) (hI47 : I47Statement) (hR1 : F112R1PlusLocStatement) :
    A38c12.FieldOne146 :=
  A38c18.fieldOne146_of_stageTheorem1427Field
    (SzPS8.stageTheorem1427Field_of_leaves_R1PlusLoc h38c h11 h113 h311 h37 h38 h39 h36 h312
      hF318 h129 hSL2 h56 hcover hG2c hA21 hB42 hB45 hD310 hRigid hI47 hR1)

end CFSG.Quasithin

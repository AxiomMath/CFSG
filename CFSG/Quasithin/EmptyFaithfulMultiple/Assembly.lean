module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1542
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma3213Local
public import CFSG.Quasithin.EmptyFaithfulMultiple.Theorem1548
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15413
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15414
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15417
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422
public import CFSG.Quasithin.Background.E2InputE213
public import CFSG.Quasithin.Background.F6F613
public import CFSG.Quasithin.Background.G64C512
public import CFSG.Quasithin.Background.G64Proof
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputsSuzuki
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputsSuzuki2
public import CFSG.Quasithin.Background.A3FactsSchreierFinal
public import CFSG.Quasithin.EmptyFaithfulMultiple.Facts134E9Proof
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Native
public import CFSG.Quasithin.EmptyFaithfulMultiple.Final15424
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1546
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15410
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1542Four
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputsProved
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15418
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15415
public import CFSG.Quasithin.Background.F6CatResidualOpen
public import CFSG.Quasithin.Vol2.GoldschmidtF134J4
public import CFSG.Quasithin.Vol2.F134LieU3
public import CFSG.Quasithin.Vol2.F134LieL3
public import CFSG.Quasithin.Vol2.F134LieSp4
public import CFSG.Quasithin.Vol2.F134LieF4
public import CFSG.Quasithin.Vol2.F134LieD4
public import CFSG.Quasithin.Vol2.F134LieG2
public import CFSG.Quasithin.Vol2.F134LieOdd
public import CFSG.Quasithin.Background.GoldschmidtAmalgam
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418Proof
public import CFSG.Quasithin.EmptyFaithfulMultiple.SylowCenterSLEps3
public import CFSG.Quasithin.EmptyFaithfulMultiple.HeAutCentralizer

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin

theorem isUniqueM_normalizer_of_isXi_of_hyp {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (h2 : Stmt1542Two G T) (X : Subgroup G)
    (hX : IsXi T X) : IsUniqueM (X ⊔ T) (Subgroup.normalizer (X : Set G)) :=
  isUniqueM_normalizer_of_isXi_of_solvable_of_evenCharacteristic hyp.sylow hyp.qtke.2.2 hX
    hyp.qtke.2.1 fun M hM => h2 M ⟨hM.1, le_sup_right.trans hM.2⟩

theorem multipleCentralizerRecognition_of_inputs
    (h56 : AsB56) (hGold : F6.GoldschmidtCharTwoLarge.{0}) :
    MultipleCentralizerRecognitionStatement := by
  have hlist : F6.GoldschmidtS3ListCat.{0} := F6.goldschmidtS3ListCat_of_charTwoLarge hGold
  have hF618R := F6.f618ResidualRest_of_remaining (F6.f618ResidualRemaining_of_goldschmidt hlist)
  have h311 := input311Solvable_of (G64.inputC512G64_of_lemmaG64 (G64.lemmaG64_of_b5 h56))
  have hF618 : F6.TheoremF618Cat := F6.theoremF618Cat_of_residualRest hF618R
  have hC421 := componentComparison15421_of_b56 h56 hF618
  have hInsp := inspection15418_of_b56 h56 hF618 sylowCenterCyclicSLEps3_holds
  intro G _ _ T hyp
  by_contra hnot
  have hJ4 := A3Facts.sporadicSchreierCase_J4_native
  have h1 := stmt1542One_of (input1413_of_J4 hJ4) (input127Three_of_J4 hJ4) hyp
  have h2 := stmt1542Two_of hyp h1
  have h137 := isUniqueM_normalizer_of_isXi_of_hyp hyp h2
  have h4 := stmt1542Four_of inputE213Solvable_holds h311 hyp h2
  have h3 := stmt1542Three_of_xiMinus hyp h1 h137 (stmt3213_of_four hyp h2 h4 h137)
  have h43 := stmt1543_of inputC226_holds hyp h2 h3 h4
  have h44 := stmt1544_of hyp h2 h3 h43
  have h45 := stmt1545_of hyp h2 h3 h43 h44
  have h49 := stmt1549_of hyp h2 h3 h45
  have h48 := stmt1548_of hyp h45 h49 (stmt15410_of hyp h2 h3 h4 h45 h137)
  have h411 := stmt15411_of hyp h48 (stmt1546_of h311 hyp h2)
  have h412 := stmt15412_of hyp h2 h48 h411
  have h47 := stmt1547_of inputGNC128Solv_holds input1391_holds inputI41Two_holds hyp h2
  have h414 := stmt15414_of hyp h3 h47 h48 h411 h412
  have h415 := stmt15415_of hlist hyp h412 (stmt15413_of hyp) h414
  have h418 := stmt15418_of hInsp hyp h48 h412 h414 h415 (stmt15416_of h311 hyp h2 h412)
    (stmt15417_of hyp)
  have h419 := stmt15419_of hyp hnot h48 h412 h414
  have h36 := CFSG.QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved
  have h37 := CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved
  have h38 := CFSG.QuasithinUnique.Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact
    CFSG.QuasithinUnique.Vol2Native.a134SQTKFactCat h36 h37
  have h134 := prop134E9He_of h36 h37 h38 P134.theoremCSimple
    (P134.facts134E9He_of_rest ({ toFacts134E9Lie := { psl3Plus := P134.facts134E9_psl3Plus,
                                                       psu3Minus := P134.facts134E9_psu3Minus,
                                                       psl3Even := P134.facts134E9_psl3Even,
                                                       psu3Even := P134.facts134E9_psu3Even,
                                                       psp4Even := P134.facts134E9_psp4Even,
                                                       g2Even := P134.facts134E9_g2Even,
                                                       d4Even := P134.facts134E9_d4Even,
                                                       f4Even := P134.facts134E9_f4Even },
                                  j4 := P134.facts134E9_j4 }))
  have h420 := stmt15420_of_b56 (facts15420_holds h56 heAutCentralizer_holds) h56 h134 hyp hnot
    h2 h48 h412 h414 (stmt15416_of h311 hyp h2 h412) (stmt15417_of hyp) h419
  have h421 := stmt15421_of inputB19_holds hC421 hyp h48 h412 h419 h420
  have h422 := stmt15422_of hF618 hyp hnot h412 h414 (stmt15417_of hyp) h419 h420
  have h423 := stmt15423_of hyp h412 h419 h421 h422
  exact false_of_stmts hyp hnot h48 h411 h412 h418 h419 h420 h422 h423

end CFSG.Quasithin.EmptyFaithfulMultiple

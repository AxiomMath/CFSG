module

public import CFSG.Quasithin.EmptyFaithful.S151cA1
public import CFSG.Quasithin.EmptyFaithful.T1515Der5
public import CFSG.Quasithin.EmptyFaithful.T1515C6Top
public import CFSG.Quasithin.EmptyFaithful.T1515C7Fin
public import CFSG.Quasithin.EmptyFaithful.T1515M11D4
public import CFSG.Quasithin.EmptyFaithful.T1515M11U

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem construction1516Four_of_ce (h15 : StageLemma1515CE) (h17 : StageLemma1517)
    (h19 : StageLemma1519) (h113 : StageLemma15113) : Construction1516Four := by
  intro G _ _ T Mc M hq hM hCE h4
  exact exists_setting_four hq hM h4 (h15 G T Mc M hq hM hCE) (h17 G T Mc M hq hM hCE)
    (h19 G T Mc M hq hM hCE) (h113 G T Mc M hq hM hCE).four

theorem construction1516Six_of_ce (h15 : StageLemma1515CE) (h19 : StageLemma1519)
    (h110 : StageLemma15110) (h113 : StageLemma15113) (h5 : Construction1516SixFive) :
    Construction1516Six := by
  intro G _ _ T Mc M hq hM hCE ⟨p, hp, h6⟩
  rcases hp with rfl | rfl
  · exact exists_setting_six3 hq hM h6 (h15 G T Mc M hq hM hCE) (h19 G T Mc M hq hM hCE)
      (h110 G T Mc M hq hM hCE h6) (h113 G T Mc M hq hM hCE).four
  · exact h5 G T Mc M hq hM hCE h6

theorem construction1516Seven_of_ce (h15 : StageLemma1515CE) (h19 : StageLemma1519)
    (h113 : StageLemma15113) : Construction1516Seven := by
  intro G _ _ T Mc M hq hM hCE h7
  exact exists_setting_seven hq hM h7 (h15 G T Mc M hq hM hCE) (h19 G T Mc M hq hM hCE)
    (h113 G T Mc M hq hM hCE).four

theorem theorem1515_of_inputs3_ce (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hCons : Construction1516) (h15 : StageLemma1515CE) (h19s : StageLemma1519)
    (h110 : StageLemma15110) (h14 : StageLemma15114) (hD : M11TypesDisjoint1522)
    (hI19 : Lemma15119InputRest') (hI20 : Lemma15120Input) (hI21 : Lemma15121Input)
    (hI22 : Lemma15122Input) (hI23 : Lemma15123Input) (hI24 : Lemma15124Input)
    (hI25 : Lemma15125InputRest) (hI27 : Lemma15127Input) (hI28 : Lemma15128Input)
    (hI29 : Lemma15129Input) : StageTheorem1515 := by
  have h1416 : StageLemma1416 := stageLemma1416_of_a3 h37 h38 h39
  intro G _ _ T Mc M hq hM hCE hce
  obtain ⟨Z₁, Z₂, V₁, V₂, hSX⟩ := hCons.exists_setting hq hM hCE hce
  have hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂ := hSX.toSetting1516
  have hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ := ⟨hq, hM, hCE, hS⟩
  have h15' := h15 G T Mc M hq hM hCE
  have h14' := h14 G T Mc M hq hM hCE
  have h19' := h19s G T Mc M hq hM hCE
  have h17 := lemma_15_1_17 hq hM hS h19'
  have h18c := lemma_15_1_18 as116Statement hC hSX.toExtra h15' h14' h19' h17
  have h19c := lemma_15_1_19_of_input_rest' h37 h38 hI19 hC h17 h18c
  obtain ⟨L, hLc, hLq, hLn⟩ := h19c.six
  have hL : IsL1519 Mc Z₁ L := ⟨hLc, hLq, hLn⟩
  have hL20 : IsL1520 T Mc Z₁ L := hL.isL1520 h18c.four (hS.pCore_g1_ne_bot hq hM)
  have h20 := lemma_15_1_20 hI20 hC (h1416 G T Mc hq).1 h15' h17 h18c h19c hL20
  have h21 := lemma_15_1_21 hI21 hC h17 h18c h19c (L := L)
  have h22 := lemma_15_1_22 hI22 hC h17 h18c h19c hL h20 h21
  have h23 := lemma_15_1_23 hI23 h110 hC h17 h18c h19c hL h22
  have h24 := lemma_15_1_24 hI24 hC h17 h18c h19c hL h22 h23 h15'
  have h25 := lemma_15_1_25_of_input_rest hD hI25 hC h15' h19' h17 h18c h19c hL h22 h24
  have h26 := lemma_15_1_26 hL h22 h24 h25
  have h27 := lemma_15_1_27 hI27 hC h17 h18c h19c hL h22 h24 h25 h26
  have h28 := lemma_15_1_28 hI28 hC h17 h18c h19c hL h22 h24 h25 h26 h27
  have h29 := lemma_15_1_29 hI29 hC h17 h18c h19c hL h22 h24 h25 h26 h27 h28
  exact h29 h28.1

theorem theorem1515_of_inputs_ce
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hC65 : Construction1516SixFive)
    (h316 : Theorem316Statement) (h317 : Theorem317Statement) (h319 : Lemma319Statement)
    (h1414 : StageLemma1414) (h1416 : StageLemma1416) (h1417 : StageLemma1417)
    (hD : Description1512CE) (hN : Nilpotency1512CE) (hStep : Step1514Gen)
    (h17 : StageLemma1517) (h158 : StageLemma1518) (h1511one : StageLemma15111One)
    (h1512four : StageLemma15112Four)
    (hI19 : Lemma15119Input25) (hI20 : Lemma15120Input) (hI21 : Lemma15121Input)
    (hI22 : Lemma15122Input) (hI23 : Lemma15123Input) (hI24 : Lemma15124Input)
    (hI25 : Lemma15125InputRest) (hI27 : Lemma15127Input) (hI28 : Lemma15128Input)
    (hI29 : Lemma15129Input) : StageTheorem1515 := by
  obtain ⟨-, h15, -, h19, -, h113, h14⟩ :=
    stage151_of_inputs_ce h316 h317 h319 h1414 h1416 h1417 hD hN hStep h17 h158 h1511one h1512four
  have h110 : StageLemma15110 := stageLemma15110_of_ce h1416 h15
  exact theorem1515_of_inputs3_ce h37 h38 h39
    ⟨construction1516Four_of_ce h15 h17 h19 h113,
      construction1516Six_of_ce h15 h19 h110 h113 hC65,
      construction1516Seven_of_ce h15 h19 h113⟩
    h15 h19 h110 h14 (m11TypesDisjoint1522_of_orders psuThreeThreeOrder1522 threeD4TwoOrder1522)
    (lemma15119InputRest'_of_input235 (lemma15119Input235_of_input25 hI19)) hI20 hI21 hI22 hI23
    hI24 hI25 hI27 hI28 hI29

end CFSG.Quasithin

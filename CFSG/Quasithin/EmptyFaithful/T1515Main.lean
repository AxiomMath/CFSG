module

public import CFSG.Quasithin.EmptyFaithful.T1515B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem lemma_15_1_28 (h : Lemma15128Input) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (h17 : Lemma15117Concl T M Z₁)
    (h18 : Lemma15118Concl T Mc M Z₁) (h19 : Lemma15119Concl T Mc M Z₁ V₂)
    (hL : IsL1519 Mc Z₁ L) (h22 : Lemma15122Concl T Mc M Z₁ L)
    (h24 : Lemma15124Concl T Mc M Z₁ V₁ V₂ L) (h25 : Lemma15125Concl T Z₁ V₁ L)
    (h26 : Lemma15126Concl L) (h27 : Lemma15127Concl Z₂ L) : Lemma15128Concl T Mc Z₁ Z₂ L :=
  h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24 h25 h26 h27

theorem lemma_15_1_29 (h : Lemma15129Input) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (h17 : Lemma15117Concl T M Z₁)
    (h18 : Lemma15118Concl T Mc M Z₁) (h19 : Lemma15119Concl T Mc M Z₁ V₂)
    (hL : IsL1519 Mc Z₁ L) (h22 : Lemma15122Concl T Mc M Z₁ L)
    (h24 : Lemma15124Concl T Mc M Z₁ V₁ V₂ L) (h25 : Lemma15125Concl T Z₁ V₁ L)
    (h26 : Lemma15126Concl L) (h27 : Lemma15127Concl Z₂ L) (h28 : Lemma15128Concl T Mc Z₁ Z₂ L) :
    Lemma15129Concl Z₂ L :=
  h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24 h25 h26 h27 h28

theorem theorem1515_of_inputs (hCons : Construction1516) (h116 : AS116Statement)
    (h15 : StageLemma1515) (h19s : StageLemma1519) (h110 : StageLemma15110)
    (h14 : StageLemma15114) (h1416 : StageLemma1416) (hI19 : Lemma15119Input)
    (hI20 : Lemma15120Input) (hI21 : Lemma15121Input) (hI22 : Lemma15122Input)
    (hI23 : Lemma15123Input) (hI24 : Lemma15124Input) (hI25 : Lemma15125Input)
    (hI27 : Lemma15127Input) (hI28 : Lemma15128Input) (hI29 : Lemma15129Input) :
    StageTheorem1515 := by
  intro G _ _ T Mc M hq hM hCE hce
  obtain ⟨Z₁, Z₂, V₁, V₂, hSX⟩ := hCons.exists_setting hq hM hCE hce
  have hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂ := hSX.toSetting1516
  have hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ := ⟨hq, hM, hCE, hS⟩
  have h15' := h15 G T Mc M hq hM
  have h14' := h14 G T Mc M hq hM hCE
  have h19' := h19s G T Mc M hq hM hCE
  have h17 := lemma_15_1_17 hq hM hS h19'
  have h18c := lemma_15_1_18 h116 hC hSX.toExtra h15' h14' h19' h17
  have h19c := lemma_15_1_19 hI19 hC h17 h18c
  obtain ⟨L, hLc, hLq, hLn⟩ := h19c.six
  have hL : IsL1519 Mc Z₁ L := ⟨hLc, hLq, hLn⟩
  have hL20 : IsL1520 T Mc Z₁ L := hL.isL1520 h18c.four (hS.pCore_g1_ne_bot hq hM)
  have h20 := lemma_15_1_20 hI20 hC (h1416 G T Mc hq).1 h15' h17 h18c h19c hL20
  have h21 := lemma_15_1_21 hI21 hC h17 h18c h19c (L := L)
  have h22 := lemma_15_1_22 hI22 hC h17 h18c h19c hL h20 h21
  have h23 := lemma_15_1_23 hI23 h110 hC h17 h18c h19c hL h22
  have h24 := lemma_15_1_24 hI24 hC h17 h18c h19c hL h22 h23 h15'
  have h25 := lemma_15_1_25 hI25 hC h17 h18c h19c hL h22 h24
  have h26 := lemma_15_1_26 hL h22 h24 h25
  have h27 := lemma_15_1_27 hI27 hC h17 h18c h19c hL h22 h24 h25 h26
  have h28 := lemma_15_1_28 hI28 hC h17 h18c h19c hL h22 h24 h25 h26 h27
  have h29 := lemma_15_1_29 hI29 hC h17 h18c h19c hL h22 h24 h25 h26 h27 h28
  exact h29 h28.1

end CFSG.Quasithin

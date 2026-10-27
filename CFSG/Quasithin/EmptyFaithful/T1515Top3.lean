module

public import CFSG.Quasithin.EmptyFaithful.T1515Top2
public import CFSG.Quasithin.EmptyFaithful.T1515Der3
public import CFSG.Quasithin.EmptyFaithful.S1416

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

structure Lemma15119Rest' (T Mc M Z₁ : Subgroup G) : Prop where
  two : ∀ K : Subgroup G, K ≤ g1_1516 Z₁ → Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) →
    mZ1516 Mc Z₁ ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ mZ1516 Mc Z₁
  three : oTwoFIn (g1_1516 Z₁) ≤ mZ1516 Mc Z₁
  five : solvRad (g1_1516 Z₁) ≤ mZ1516 Mc Z₁
  six : ∃ L : Subgroup G, L ∈ cComp (g1_1516 Z₁) ∧
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧ ¬ L ≤ mZ1516 Mc Z₁

@[expose] def Lemma15119InputRest' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    oddCoreIn (g1_1516 Z₁) = ⊥ →
    (∀ H : Subgroup G, mZ1516 Mc Z₁ ≤ H → H ≤ g1_1516 Z₁ → oTwoFstarIn H ≤ mZ1516 Mc Z₁ →
      H = mZ1516 Mc Z₁) →
    Lemma15119Rest' T Mc M Z₁

theorem lemma_15_1_19_of_input_rest' (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h : Lemma15119InputRest')
    {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G} (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂)
    (h17 : Lemma15117Concl T M Z₁) (h18 : Lemma15118Concl T Mc M Z₁) :
    Lemma15119Concl T Mc M Z₁ V₂ := by
  have hR := h G T Mc M Z₁ Z₂ V₁ V₂ hC h17 h18 (lemma_15_1_19_one hC.qtfe hC.mf hC.setting h18)
    (lemma_15_1_19_four h18.five.2.1)
  exact ⟨lemma_15_1_19_one hC.qtfe hC.mf hC.setting h18, hR.two, hR.three,
    lemma_15_1_19_four h18.five.2.1, hR.five, hR.six,
    lemma_15_1_19_seven h37 h38 hC.qtfe hC.mf hC.setting⟩

theorem theorem1515_of_inputs3 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hCons : Construction1516) (h15 : StageLemma1515) (h19s : StageLemma1519)
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
  have h15' := h15 G T Mc M hq hM
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

end CFSG.Quasithin

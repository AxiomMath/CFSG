module

public import CFSG.Quasithin.EmptyFaithful.T1515Top3
public import CFSG.Quasithin.EmptyFaithful.T1515Der4
public import CFSG.Quasithin.EmptyFaithful.T1515M11

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

structure Lemma15119Rest235 (T Mc M Z₁ : Subgroup G) : Prop where
  two : ∀ K : Subgroup G, K ≤ g1_1516 Z₁ → Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) →
    mZ1516 Mc Z₁ ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ mZ1516 Mc Z₁
  three : oTwoFIn (g1_1516 Z₁) ≤ mZ1516 Mc Z₁
  five : solvRad (g1_1516 Z₁) ≤ mZ1516 Mc Z₁

@[expose] def Lemma15119Input235 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    oddCoreIn (g1_1516 Z₁) = ⊥ →
    (∀ H : Subgroup G, mZ1516 Mc Z₁ ≤ H → H ≤ g1_1516 Z₁ → oTwoFstarIn H ≤ mZ1516 Mc Z₁ →
      H = mZ1516 Mc Z₁) →
    Lemma15119Rest235 T Mc M Z₁

theorem lemma15119InputRest'_of_input235 (h : Lemma15119Input235) : Lemma15119InputRest' := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ hC h17 h18 hO h4
  have hR := h G T Mc M Z₁ Z₂ V₁ V₂ hC h17 h18 hO h4
  exact ⟨hR.two, hR.three, hR.five, lemma_15_1_19_six_of_three_four hC.qtfe h18 hR.three h4⟩

theorem lemma_15_1_19_of_input_235 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h : Lemma15119Input235)
    {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G} (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂)
    (h17 : Lemma15117Concl T M Z₁) (h18 : Lemma15118Concl T Mc M Z₁) :
    Lemma15119Concl T Mc M Z₁ V₂ :=
  lemma_15_1_19_of_input_rest' h37 h38 (lemma15119InputRest'_of_input235 h) hC h17 h18

theorem theorem1515_of_inputs4
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hCons : Construction1516) (h15 : StageLemma1515) (h19s : StageLemma1519)
    (h110 : StageLemma15110) (h14 : StageLemma15114)
    (hU : PSUThreeThreeOrder) (hD : ThreeD4TwoOrder)
    (hI19 : Lemma15119Input235) (hI20 : Lemma15120Input) (hI21 : Lemma15121Input)
    (hI22 : Lemma15122Input) (hI23 : Lemma15123Input) (hI24 : Lemma15124Input)
    (hI25 : Lemma15125InputRest) (hI27 : Lemma15127Input) (hI28 : Lemma15128Input)
    (hI29 : Lemma15129Input) : StageTheorem1515 :=
  theorem1515_of_inputs3 h37 h38 h39 hCons h15 h19s h110 h14 (m11TypesDisjoint1522_of_orders hU hD)
    (lemma15119InputRest'_of_input235 hI19) hI20 hI21 hI22 hI23 hI24 hI25 hI27 hI28 hI29

end CFSG.Quasithin

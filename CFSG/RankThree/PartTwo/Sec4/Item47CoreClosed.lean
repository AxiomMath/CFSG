module

public import CFSG.RankThree.PartTwo.Sec4.Item47Close
public import CFSG.RankThree.PartTwo.Sec4.Item47CoreOut
public import CFSG.RankThree.PartTwo.Sec4.Item47WitnessG2
public import CFSG.RankThree.PartTwo.Sec4.Item47WitnessU4
public import CFSG.RankThree.PartOne.RF4.FinalKFacts

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Statements


@[expose] def Inputs47WitnessD4 : Prop :=
  ∀ (X : Type) [Group X] (k : ℕ),
    Blueprint.ChevalleyExceptionalModel X .trialityD4 2 (2 * k) →
    ∀ α : MulAut X, α ^ 3 = 1 → ¬ IsInnerAut α → HasLocalWitness α

@[expose] def Inputs47ClassesD4 : Prop :=
  ∀ n : ℕ, Odd n → ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ n) ^ 3 → (∀ c, σ c = c ^ 2 ^ n) →
    ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      α ^ 3 = 1 → ¬ IsInnerAut α →
        IsStdGraphFieldConj σ α ∨
          ∃ (γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
            (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
            IsStdGraphFieldConj σ γ ∧ γ y = y ∧ orderOf y = 3 ∧ α = γ * MulAut.conj y ∧
              Sec8.IsoPGUThree (autFix α) (2 ^ n)

end Statements

section Assembly

theorem inputs47Core_of_d4
    (hw : Inputs47WitnessD4) (hc : Inputs47ClassesD4) : Inputs47Core where
  outG23 := inputs47Core_outG23
  outJ4 := inputs47Core_outJ4
  outON := inputs47Core_outON
  witnessG2 := inputs47Core_witnessG2
  witnessD4 := hw
  witnessU4 := inputs47Core_witnessU4
  classesD4 := hc
  reeLang := fun a K _ _ _ _ hK => CFSG.RankThree.PartOne.RF4.largeReeOrderThreeFieldConj a K hK

theorem rank3II_4_7_of_d4
    (h46 : Item4_6) (hw : Inputs47WitnessD4) (hc : Inputs47ClassesD4) : Item4_7 :=
  rank3II_4_7_of_core h46 (inputs47Core_of_d4 hw hc)

end Assembly

section NoD4


theorem inputs47NoD4 : Inputs47NoD4 where
  outU4p := outU4p_holds
  outU54 := outU54_holds
  outG23 := inputs47Core_outG23
  outU43 := outU43_holds
  outTits X _ f hX := by
    rw [card_outer_tits X f hX]
    norm_num
  outSporadic := not_three_dvd_card_outer_sporadic46 inputs47Core_outJ4 inputs47Core_outON
  centerSporadic _ hs := center_carrier_eq_bot_of_cover hs
  witnessG2 := inputs47Core_witnessG2
  witnessU4 := inputs47Core_witnessU4
  reeLang := fun a K _ _ _ _ hK => CFSG.RankThree.PartOne.RF4.largeReeOrderThreeFieldConj a K hK

theorem rank3II_4_7W_of (h46 : Item4_6) : Item4_7W :=
  rank3II_4_7W_of_noD4 h46 inputs47NoD4

end NoD4

end CFSG.RankThree.PartTwo.Sec4

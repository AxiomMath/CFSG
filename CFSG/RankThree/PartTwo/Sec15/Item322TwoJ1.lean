module

public import CFSG.RankThree.PartTwo.Sec15.Item322ScopeProof
public import CFSG.RankThree.PartTwo.Sec15.Item15Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS

@[expose] def Item3_22TwoJ1 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], generalizedFitting X = CFSG.pCore 2 X →
    Nonempty (X ⧸ CFSG.pCore 2 X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ R : Subgroup X, CFSG.pCore 2 X ≤ R →
      Nonempty (R.map (QuotientGroup.mk' (CFSG.pCore 2 X)) ≃*
        Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
      Nonempty (Subgroup.centralizer
          ((R.map (QuotientGroup.mk' (CFSG.pCore 2 X)) : Subgroup (X ⧸ CFSG.pCore 2 X)) :
            Set (X ⧸ CFSG.pCore 2 X)) ≃*
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × alternatingGroup (Fin 5)) →
      ¬ (omegaOneCenter (⊤ : Subgroup R)).map R.subtype ≤ Subgroup.center X →
        ((higherElemThompson R 1).map R.subtype).Normal

theorem item3_22Two_of_J1
    (h : Item3_22TwoJ1) : Item3_22Two :=
  fun X _ _ hF hJ R hQR hE hC hz =>
    ⟨item3_22TwoJ_holds X hF hJ R hQR hE hC hz, h X hF hJ R hQR hE hC hz⟩

end CFSG.RankThree.PartTwo.Sec15

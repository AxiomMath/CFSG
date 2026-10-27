module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.HigherElementaryThompson
public import CFSG.GH74.GLS.Basic
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS

@[expose] def Item3_22TwoJ : Prop :=
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
        ((higherElemThompson R 0).map R.subtype).Normal

end CFSG.RankThree.PartTwo.Sec15

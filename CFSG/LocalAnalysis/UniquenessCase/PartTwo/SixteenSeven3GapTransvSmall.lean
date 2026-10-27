module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def S16GapTransvectionSmall (D : Data G) : Prop :=
  ∀ (V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D ⊥ V L hV →
    Case168_2Small D ⊥ V hV L → ∀ A : Subgroup G, Choice1613 D ⊥ V hV L A →
      ∀ g : G, A ≤ conjSubgroup V g → V ≤ conjSubgroup D.M g → ¬ conjSubgroup V g ≤ D.M →
        rk ↥(barSub ⊥ V hV A) ≤ 2 →
          E3.mQuot V (V ⊓ centralizer (conjSubgroup V g : Set G)) ≤ D.k + 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Quasithin.EmptyFaithful.S152He2Module

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Insp15227TransLn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M H : Subgroup G), Setting152 T Mc M → IsHStar T M H →
    ¬ V154 T Mc M ≤ pCoreOf 2 Mc →
    (Case15212ii T Mc (conjClosure (oTwoUpper H) Mc) ∨
      Case15212iii T Mc (conjClosure (oTwoUpper H) Mc)) →
    ∀ L N : Subgroup G, IsChiefStep (conjClosure (oTwoUpper H) Mc ⊔ T) (pCoreOf 2 Mc) L N →
      Nat.card ↥(⁅N, V154 T Mc M⁆ ⊔ L) ≠ 2 * Nat.card ↥L

@[expose] def Insp15227Trans : Prop := Insp15227TransLn ∧ HeNoSmallCommutatorModule

end CFSG.Quasithin

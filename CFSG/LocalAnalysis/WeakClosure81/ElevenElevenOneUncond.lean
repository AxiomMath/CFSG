module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenCount
public import CFSG.LocalAnalysis.WeakClosure81.ElevenOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

theorem w3Thm111_unconditional :
    ∀ M V Q : Subgroup G, Setting11 M V Q → MBarGT M ⊥ V 2 →
      ∀ n : ℕ, MBarGT M ⊥ V n → (n : ℕ∞) < rMV M V :=
  w3Thm111_of_closing fun _ _ _ _ => eleven11Closing_holds

end CFSG.LocalAnalysis.WeakClosure81

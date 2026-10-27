module

public import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.KFacts.L34OuterThreeConj
import CFSG.RankThree.PartTwo.KFacts.L34OuterThreeFive
import CFSG.RankThree.PartTwo.KFacts.L34OuterThreeSeven

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

variable {k : Type*} [Field k]

theorem exists_orderOf_five_or_seven_fixed (hk : Nat.card k = 4) {X : Type*} [Group X]
    (χ : X ≃* projectiveSL 3 k) {α : MulAut X} (hα : orderOf α = 3)
    (hout : α ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ y : X, (orderOf y = 5 ∨ orderOf y = 7) ∧ α y = y :=
  exists_orderOf_five_or_seven_fixed_of_witnesses hk
    (fun _ hu => exists_orderOf_five_fixed_xDiag hk hu)
    (fun _ hu => exists_orderOf_seven_fixed_xDiag_mul_yInn hk hu)
    (fun _ hu => exists_orderOf_seven_fixed_xDiag_mul_yInn_sq hk hu) χ hα hout

theorem exists_orderOf_five_or_seven_fixed_projSL {X : Type*} [Group X]
    (χ : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) {α : MulAut X}
    (hα : orderOf α = 3) (hout : α ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ y : X, (orderOf y = 5 ∨ orderOf y = 7) ∧ α y = y :=
  exists_orderOf_five_or_seven_fixed card_galoisField_two_two
    (χ.trans (projSLEquivProjectiveSL 3 (GaloisField 2 2))) hα hout

end CFSG.RankThree.PartTwo.KFacts.L34

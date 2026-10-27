module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

@[expose] def SumOfNatShape (L : Subgroup (MulAut W)) (U Z : Subgroup W) (k : ℕ) : Prop :=
  ∃ n : ℕ,
    (IsSLn ↥L n 1 ∧ SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) L U Z k) ∨
    (IsSpn ↥L n 1 ∧ SumOfNat (fun H U Z => NatSpn H U Z n 1) L U Z k) ∨
    (IsOmegaPlus ↥L n 1 ∧ SumOfNat (fun H U Z => NatOmegaPlus H U Z n 1) L U Z k) ∨
    (IsOmegaMinus ↥L n 1 ∧ SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1) L U Z k) ∨
    (UC22.IsAlt ↥L n ∧ SumOfNat (fun H U Z => AlternatingNatural H U Z n) L U Z k)

theorem sumOfAtMostThreeNat_iff (L : Subgroup (MulAut W)) (U Z : Subgroup W) :
    SumOfAtMostThreeNat L U Z ↔ ∃ k : ℕ, k ≤ 3 ∧ SumOfNatShape L U Z k :=
  Iff.rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

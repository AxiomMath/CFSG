module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def K_SU44_TwoNat : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ X Y : Subgroup (MulAut W), X ≤ Y → Y ≤ normalizer (X : Set (MulAut W)) →
      IsSUn ↥X 4 2 →
      (∃ (K : Type) (_ : Field K) (_ : Finite K) (π : ↥(StatedSU 4 (2 ^ 2) K) →* ↥X),
        Nat.card K = (2 ^ 2) ^ 2 ∧
          SumOfNatVia (CFSG.Quasithin.FFModel.nat (StatedSU 4 (2 ^ 2) K))
            X ⊤ ⊥ 2 π) →
      8 ≤ CFSG.Quasithin.E3.mParam Y ∧
      CFSG.Quasithin.E3.aSet 7 Y = ∅ ∧
      ¬ IsFFModule Y ∧
      ∀ S : Subgroup (MulAut W), IsSylowIn 2 S Y →
        ∃ Z : Subgroup W, Z ≠ ⊥ ∧
          (∀ A ∈ CFSG.Quasithin.E3.aSet 2 Y, A ≤ S → Z ≤ fixV A) ∧
          ∃ E : Subgroup (MulAut W), E ≤ X ⊓ stabSub Z ∧
            IsElemAbelian 5 E ∧ Nat.card E = 25

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

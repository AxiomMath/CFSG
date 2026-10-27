module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

@[expose] def Sp4TwoNatData (H : Subgroup (MulAut W)) (f : ℕ) : Prop :=
  IsSp4 ↥H f ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (π : ↥(StatedSp 2 K) →* ↥H),
      Nat.card K = 2 ^ f ∧
        SumOfNatVia (FFModel.nat (StatedSp 2 K)) H ⊤ ⊥ 2 π

@[expose] def K_Sp4TwoNat_involution : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (f : ℕ), Odd f → Sp4TwoNatData H f →
      ∀ t ∈ normalizer (H : Set (MulAut W)), orderOf t = 2 →
        2 * f ≤ rkIdx (fixV (zpowers t))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

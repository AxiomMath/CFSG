module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightSum

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def K_O6m4_L2FixFree : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut W)) (I : Subgroup W), IsOmegaMinus ↥X 6 2 →
      NatOmegaMinus X I ⊥ 6 2 →
      ∀ S J : Subgroup (MulAut W), IsSylowIn 2 S X → S ≤ J → J ≤ X →
        IsL2 (Bar2 J) 2 → I ⊓ fixV J = ⊥

theorem fixV_eq_bot_of_sumOfNat_omegaMinus (hK : K_O6m4_L2FixFree) {W : Type} [CommGroup W]
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {X S J : Subgroup (MulAut W)}
    (hO : IsOmegaMinus ↥X 6 2)
    (hS : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 2) X ⊤ ⊥ 3)
    (hSyl : IsSylowIn 2 S X) (hSJ : S ≤ J) (hJX : J ≤ X) (hL2 : IsL2 (Bar2 J) 2) :
    fixV J = ⊥ := by
  have h := s16e_inf_fixV_eq_bot_of_sumOfNat (N := fun _ I Z => NatOmegaMinus X I Z 6 2)
    (H := J) (U := ⊤) (k := 3) ?_ ?_ hS
  · simpa using h
  · intro I hI x u hu
    obtain ⟨-, K, _, _, b, c, -, -, π, hπ⟩ := hI
    exact hπ.2.2.2.1 ⟨x, hJX x.2⟩ u hu
  · intro I hI
    exact hK W hW X I hO hI S J hSyl hSJ hJX hL2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

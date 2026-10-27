module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section KitF

variable {W : Type} [CommGroup W]

@[expose] def OmegaFormExists (H : Subgroup (MulAut W)) : Prop :=
  ∃ Q : W → ZMod 2, IsMinusQuadF2 Q ∧ QuadInvariant Q H

@[expose] def OmegaSingE16A5 (H : Subgroup (MulAut W)) : Prop :=
  ∀ w : W, w ≠ 1 → Nat.card (ptCent H w) = 960 → IsE16A5 ↥(ptCent H w)

@[expose] def OmegaNonsSym (H : Subgroup (MulAut W)) : Prop :=
  ∀ w : W, w ≠ 1 → Nat.card (ptCent H w) ≠ 960 → IsSym ↥(ptCent H w) 6

end KitF

@[expose] def OmegaKitF : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)),
    NatOmegaMinus H (⊤ : Subgroup W) ⊥ 6 1 →
      OmegaFormExists H ∧ OmegaSingE16A5 H ∧ OmegaNonsSym H

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

@[expose] def s16h_SimpleScalar (H : Subgroup (MulAut W)) (U Z : Subgroup W) : Prop :=
  IsIrrOn H U Z ∧
    ∀ f : Sec U Z →* Sec U Z, (∀ g ∈ autSec H U Z, ∀ x : Sec U Z, f (g x) = g (f x)) →
      f = 1 ∨ f = MonoidHom.id (Sec U Z)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

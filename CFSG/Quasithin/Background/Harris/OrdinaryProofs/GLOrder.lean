module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

noncomputable def glvEquivMatrix [Module.Finite (ZMod 2) V] :
    GLV V ≃* Matrix.GeneralLinearGroup (Fin (Module.finrank (ZMod 2) V)) (ZMod 2) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.trans
    (Units.mapEquiv
      (LinearMap.toMatrixAlgEquiv (Module.finBasis (ZMod 2) V)).toMulEquiv))

lemma card_GLV [Module.Finite (ZMod 2) V] :
    Nat.card (GLV V) = ∏ i : Fin (Module.finrank (ZMod 2) V),
      (2 ^ Module.finrank (ZMod 2) V - 2 ^ (i : ℕ)) := by
  rw [Nat.card_congr (glvEquivMatrix (V := V)).toEquiv, Matrix.card_GL_field, ZMod.card]

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end

module

public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.Quasithin.SteinbergBS

theorem card_linearEquiv_eq_card_GL {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] :
    Nat.card (W ≃ₗ[k] W) = Nat.card (GL (Fin (Module.finrank k W)) k) := by
  classical
  let b := Module.finBasisOfFinrankEq k W rfl
  exact Nat.card_congr ((LinearMap.GeneralLinearGroup.generalLinearEquiv k W).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)).toEquiv

theorem not_dvd_card_GL_two {d : ℕ} (hd : d < 6) :
    ¬ 27 ∣ ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
  interval_cases d <;> decide

end CFSG.Quasithin.SteinbergBS

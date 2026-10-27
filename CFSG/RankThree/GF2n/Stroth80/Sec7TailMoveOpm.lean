module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.RankThree.GF2n.Stroth80

@[expose] def opm {K E : Type*} [Field K] [AddCommGroup E] [Module K E] (g : E ≃ₗ[K] E) :
    E →ₗ[K] E :=
  (g : E →ₗ[K] E) - LinearMap.id

theorem opm_apply {K E : Type*} [Field K] [AddCommGroup E] [Module K E] (g : E ≃ₗ[K] E) (x : E) :
    opm g x = g x - x := rfl

end CFSG.RankThree.GF2n.Stroth80

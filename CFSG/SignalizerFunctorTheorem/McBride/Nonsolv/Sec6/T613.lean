module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L611
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L612
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L67
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L63
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T66
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T613.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T613.Free
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T613.KFunctor
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T613.Components
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T613.Maximal

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem theorem_6_13
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) : TypeA p A θ := by
  refine ⟨T613.simple_thetaOf h hS, fun _ hF => T613.wreath h hS hF, fun a ha ha1 => ?_,
    fun _ ha ha1 => T613.kOf_thetaOf_zpowers h hS ha ha1, fun _ hF => T613.bN_eq h hS hF⟩
  rw [h.isFunctor.thetaOf_zpowers ha ha1]
  exact T613.maximal_apply h hS ha ha1

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

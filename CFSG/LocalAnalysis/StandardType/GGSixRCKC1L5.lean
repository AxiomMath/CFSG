module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.Defs

public section

namespace CFSG.StandardType.RCKC1

theorem commute_one_add_smul_of_ne_zero {E A : Type*} [Field E] [Ring A] [Algebra E A]
    {g N : A} {c₀ : E} (hc₀ : c₀ ≠ 0) (h : Commute g (1 + c₀ • N)) (c : E) :
    Commute g (1 + c • N) := by
  have h1 : Commute g (c₀ • N) := by
    simpa using h.sub_right (Commute.one_right g)
  have h2 : Commute g N := by
    have := h1.smul_right c₀⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hc₀, one_smul] at this
  exact (Commute.one_right g).add_right (h2.smul_right c)

end CFSG.StandardType.RCKC1

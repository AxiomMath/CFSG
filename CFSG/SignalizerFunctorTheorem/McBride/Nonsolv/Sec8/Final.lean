module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T61

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

theorem false'
    (h : Counterexample p A θ) : False := by
  obtain ⟨hAB, -, -⟩ := h.theorem_6_1
  rcases hAB with hA | ⟨E, K, hB⟩
  · exact h.theorem_8_1 hA
  · exact h.typeB_false hB

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

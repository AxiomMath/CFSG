module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.Geom
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.Pair
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.WK
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.Cover
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.Max
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.Fam
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.Order
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.Fix
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.Close

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

theorem typeB_false
    (h : Counterexample p A θ) {E K : Subgroup G} (hB : TypeB p A θ E K) :
    False := by
  obtain ⟨F₁, F₂, hT⟩ := TB.TwoLines.exists_twoLines h hB.mem
  exact TB.false_of_twoLines h hB hT

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

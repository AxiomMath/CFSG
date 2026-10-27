module

public import CFSG.RankThree.GF2n.Stroth80.Sec8Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Sec7VtIrredStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ U : Subgroup G, Z ≤ U → U ≤ Vt M (LB M Q B) B Z t →
      (∀ r ∈ Rt M (LB M Q B) t, ∀ u ∈ U, r * u * r⁻¹ ∈ U) →
      U = Z ∨ U = Vt M (LB M Q B) B Z t

@[expose] def Sec8CommWtStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ s ∈ Z0, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Z

end CFSG.RankThree.GF2n.Stroth80

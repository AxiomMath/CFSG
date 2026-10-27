module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec7Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec9Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Step93VanishSwapStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ r : G, Sec7A hc t r →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M Z0 (LB M Q B) → ∀ s z : G, Sec9T1 M Q Z0 s z →
      (∃ v ∈ Vt M (LB M Q B) B Z t, ⁅z * s * z⁻¹, v⁆ ∉ Z) →
      ∀ R₀ : Subgroup G, hc.CN t ≤ R₀ → R₀ ≤ Rt M (LB M Q B) t →
        (∀ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ R₀ = R₀) → R₀ ≠ hc.CN t →
        R₀ ≠ Rt M (LB M Q B) t → conjSubgroup (z * s * z⁻¹) R₀ ≠ R₀

@[expose] def Step93VanishCountStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ r : G, Sec7A hc t r →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M Z0 (LB M Q B) → ∀ s z : G, Sec9T1 M Q Z0 s z →
      (∃ v ∈ Vt M (LB M Q B) B Z t, ⁅z * s * z⁻¹, v⁆ ∉ Z) → n ≤ 6

end CFSG.RankThree.GF2n.Stroth80

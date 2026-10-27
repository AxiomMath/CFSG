module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFWreath
public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsDefs

public section

namespace CFSG.StandardType

@[expose] def ggAutDispl {G : Type} [Group G] (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs)) :
    Subgroup G :=
  Subgroup.closure {g | ∃ φ ∈ A, ∃ b : ↥Bs, g = ((b⁻¹ * φ b : ↥Bs) : G)}

@[expose] def GGQTwoVACOneBlock {G : Type} [Group G] (L E : Subgroup G) {H : Type} [Group H]
    (t₀ : H) : Prop :=
  ∃ e : H ≃* ↥L, ∀ d : ↥L, (d : G) ∈ E → ¬ IsConj d (e t₀)

@[expose] def GGQTwoVACConcl {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) : Prop :=
  GGQTwoI1 Bs D J ∧ GGQTwoK1 p B Bs x D J ∧
    9 ≤ Nat.card (ggAutDispl Bs (ggAutomizer J Bs)) ∧
    (GGQTwoVACOneBlock L (ggAutDispl Bs (ggAutomizer J Bs))
        (CFSG.RankThree.PartTwo.Sec4.RonanK429F.W6.T 0) ∨
      GGQTwoVACOneBlock L (ggAutDispl Bs (ggAutomizer J Bs))
        (CFSG.RankThree.PartTwo.Sec4.RonanK429F.W7.T 0))

@[expose] def GGQTwoVACCell : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ 4 ∣ Nat.card (ggAutomizer J Bs) →
      GGQTwoVACConcl p B Bs x L D J

@[expose] def GGQTwoGuardFailsOn (S : ℕ → CFSG.Assembly.LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting p B Bs x L D J → p = 3 → GGInnerDiagOnLabel S p Bs L →
      4 ∣ Nat.card (ggAutomizer J Bs)

end CFSG.StandardType

end

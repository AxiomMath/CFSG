module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def B23Shape (S : Type) [Group S] : Prop :=
  (∃ a : ℕ, IsL2 S a ∨ IsSz S a) ∨
    (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsL2Odd S q) ∨ IsJ1 S

@[expose] def KSub23 : Prop :=
  (∀ (W S : Type) [Group W] [Finite W] [Group S] [Finite S] (m : ℕ),
      3 ≤ m → IsL2 W m → B23Shape S →
      ∀ Y : Subgroup S, (∃ f : W →* ↥Y, Function.Surjective f) →
        (∃ T : Sylow 2 S, ∀ t : T, (t : S) ∈ Subgroup.normalizer (Y : Set S)) →
        Y = ⊥ ∨ Y = ⊤) ∧
  (∀ (W S : Type) [Group W] [Finite W] [Group S] [Finite S] (m : ℕ),
      3 ≤ m → (IsSLn W 3 m ∨ IsSp4 W m ∨ IsU4 W m) → B23Shape S →
      ∀ Y : Subgroup S, (∃ f : W →* ↥Y, Function.Surjective f) → Y = ⊥) ∧
  (∀ (S : Type) [Group S] [Finite S], B23Shape S →
      ∀ Y : Subgroup S, ⁅Y, Y⁆ = Y →
        ∀ R : Subgroup ↥Y, R.Normal → Group.IsSolvable ↥R → R = ⊥)

@[expose] def KSub23Simple : Prop :=
  ∀ (S : Type) [Group S] [Finite S], B23Shape S → ∀ Y : Subgroup S,
    ⁅Y, Y⁆ = Y → Y = ⊥ ∨ IsSimpleGroup ↥Y

@[expose] def S23_9_B23Omega (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z → ∀ hV : IsElemAbelian 2 c.V,
    IsOmegaPlus ↥(barSub ⊥ c.V hV c.L) 6 (CFSG.Open.pRank 2 D.Z) →
    NatOmegaPlus (barSub ⊥ c.V hV c.L) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z) →
    Hinf (D.M ⊓ c.L) = ⊥ ∨ Hinf (D.M ⊓ c.L) ∈ calC D.M ∨
      ∃ X₁ X₂ : Subgroup G, X₁ ∈ calC D.M ∧ X₂ ∈ calC D.M ∧ X₁ ≠ X₂ ∧
        barImage D.M (Hinf (D.M ⊓ c.L)) = barImage D.M X₁ ⊔ barImage D.M X₂

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

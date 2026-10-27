module

public import CFSG.Quasithin.EmptyFaithful.S151XF

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Lemma15120Types (T Mc M Z₁ L : Subgroup G) : Prop :=
  IsSylowTwoOf (s1516 T Z₁ ⊓ L) L ∧ ¬ L ≤ M ∧
  (CharTwo L → ⁅L, thompsonJ (s1516 T Z₁)⁆ = L ∧
    (Case15120TwoA T Mc Z₁ L ∨
      ((L ∈ cComp (g1_1516 Z₁) →
          IsAltBlockType L 7 ∨ IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L) ∧
        ListD15120 L) ∨ Case15120TwoC Mc Z₁ L)) ∧
  (IsComponentOf L (g1_1516 Z₁) → IsPGroup 2 ↥(Subgroup.center ↥L) ∧
    (Case15120ThreeA Mc Z₁ L ∨ Case15120ThreeB Mc Z₁ L ∨ CompTypeC15120 L ∨ CompTypeD15120 L ∨
      CompTypeE15120 L ∨ IsAlt 6 ↥L ∨ IsAlt 7 ↥L))

@[expose] def Lemma15120TypesInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15120Types T Mc M Z₁ L

@[expose] def Input15120CompListCoarse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) →
    CompTypeA15120 L ∨ CompTypeB15120 L ∨ CompTypeC15120 L ∨ CompTypeD15120 L ∨
      CompTypeE15120 L ∨ IsAlt 6 ↥L ∨ IsAlt 7 ↥L

end CFSG.Quasithin.E9

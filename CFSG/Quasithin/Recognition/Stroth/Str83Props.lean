module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F3Amalgam
public import CFSG.Quasithin.EmptyFaithful.F112HypW
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.Quasithin.Recognition.Stroth.SliceSplit

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R

@[expose] def Str83RqEq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112HypW L1 L2 S → 1 ≤ a → Nonempty (oTwoQuot ↥L1 ≃* Sz a) → VBig L2 → VL2 L2 →
      IsL2Quot (2 * a + 1) (oTwoQuot ↥L2)

@[expose] def Str83Q1Order : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112HypW L1 L2 S → 1 ≤ a → Nonempty (oTwoQuot ↥L1 ≃* Sz a) →
      IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) →
      Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 10

@[expose] def Str83CaseI : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112HypW L1 L2 S → bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) → 1 ≤ a →
    Nonempty (oTwoQuot ↥L1 ≃* Sz a) → VBig L2 → VL2 L2 →
      L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤
        Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) : Set G)

@[expose] def Str83TorusFaithful : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112HypW L1 L2 S → bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) → 1 ≤ a →
    Nonempty (oTwoQuot ↥L1 ≃* Sz a) → VBig L2 → VL2 L2 →
      ∀ d ∈ borelOf L2 S, Odd (orderOf d) →
        (∀ z ∈ omegaOneCenterOf S, d * z = z * d) → d = 1

@[expose] def Str83BorelInf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112HypW L1 L2 S → 1 ≤ a → Nonempty (oTwoQuot ↥L1 ≃* Sz a) → VBig L2 → VL2 L2 →
      IsPGroup 2 ↥(borelOf L1 S ⊓ borelOf L2 S)

@[expose] def Str83PathFix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112HypW L1 L2 S → 1 ≤ a → Nonempty (oTwoQuot ↥L1 ≃* Sz a) → VBig L2 → VL2 L2 →
      ∀ (Y : Type) [Group Y] [Finite Y] (c : (f112Amalgam L1 L2 S).Completion Y),
        c.IsFaithful → ∀ p : GPath c.graph 9, p.NoBack → ∀ g : ↥(c.φ1.range ⊔ c.φ2.range),
          (∀ i, i ≤ 9 → g • p i = p i) → (∃ k : ℕ, orderOf g = 2 ^ k) → g = 1

end CFSG.Quasithin.Stroth

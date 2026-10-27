module

public import CFSG.Quasithin.H13.NQTermPrimeResidualDefs
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.H13.StatementsFSU

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

@[expose] def NoOddLinearThreeLStarF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T K : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaximalLocal T K → quasithinIsFaithfulLocal T K →
    ∀ r : ℕ, r.Prime → 3 < r →
      ¬ IsPSL 3 r 1 (↥K ⧸ CFSG.pCore 2 ↥K) ∧ ¬ IsSL3 r (↥K ⧸ CFSG.pCore 2 ↥K)

@[expose] def Lemma3_2_13Consumed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T D : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaximalLocal T D → quasithinIsFaithfulLocal T D →
    T ≤ normalizer (D : Set G) → ¬ CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D) →
    ∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) ≠ ⊥ →
      nqPrimeResidualX D p ≤ centralizer (reducedAggregate (D ⊔ T) : Set G)

@[expose] def Lemma3_2_14HomocyclicConsumed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T D : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaximalLocal T D → quasithinIsFaithfulLocal T D →
    T ≤ normalizer (D : Set G) → ¬ CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D) →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ e : ℕ, 1 < e →
      Nonempty (↥(CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D)) ≃*
        (Multiplicative (ZMod (p ^ e)) × Multiplicative (ZMod (p ^ e)))) →
      closure {x | x ∈ (CFSG.solvableRadical ↥D).map D.subtype ∧ ∃ n : ℕ, x ^ p ^ n = 1} ≤
        centralizer (reducedAggregate (D ⊔ T) : Set G)

end CFSG.Quasithin.H13.NQBlock

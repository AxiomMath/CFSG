module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCollapse
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.NQSetupDefs
public import CFSG.Quasithin.SteinbergCCLocalSylowAction
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)

@[expose] def OriginalXTPlacement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ X : Subgroup G, X ≤ (CFSG.solvableRadical L).map L.subtype →
      (X.subgroupOf L).Characteristic → CFSG.pCore 2 X ≠ ⊥ →
      CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 X →
      IsPGroup p (X ⧸ CFSG.pCore 2 X) → Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p →
      CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 →
      Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 →
      (∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1) →
      (∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
        (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
        V = ⊥ ∨ V = ⊤) →
      ∀ H : Subgroup G, X ⊔ T ≤ H → pCoreOf 2 H ≠ ⊥ → ¬ H ≤ M →
      ∃ K : Subgroup G, K ∈ cComp H ∧ quasithinIsLocal T K ∧ K ≤ H ∧ (K.subgroupOf H).Normal ∧
        X ≤ K ∧ ¬ K ≤ M ∧ quasithinGenFitting K = pCoreOf 2 K ∧
        CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) ∧
        (Nat.card (center (K ⧸ CFSG.pCore 2 K)) = 1 ∨
          Nat.card (center (K ⧸ CFSG.pCore 2 K)) = 3) ∧
        CFSG.pRank p (K ⧸ CFSG.pCore 2 K) = 2 ∧ ⁅K, X⁆ = K ∧
        pCoreOf 2 (X ⊔ T) ≤ normalizer (K : Set G) ∧
        pCoreOf 2 (H ⊓ normalizer (pCoreOf 2 (X ⊔ T) : Set G)) = pCoreOf 2 (X ⊔ T) ∧
        ∀ D : Subgroup G, D ≠ ⊥ → D ≤ pCoreOf 2 (X ⊔ T) →
          (D.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic →
          H ⊓ normalizer (D : Set G) ≤ H ⊓ M

@[expose] def CPUOffenderSection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R K M : Subgroup G), R ≤ H → IsPGroup 2 R →
    pCoreOf 2 (H ⊓ normalizer (R : Set G)) = R → K ∈ cComp H →
    quasithinGenFitting K = pCoreOf 2 K → CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) →
    R ≤ normalizer (K : Set G) → M ≤ H → ¬ K ≤ M →
    (∀ D : Subgroup G, D ≠ ⊥ → D ≤ R → (D.subgroupOf R).Characteristic →
      H ⊓ normalizer (D : Set G) ≤ M) →
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W) (_ : Nontrivial W),
      ∃ L₁ B₁ : Subgroup (Module.End (ZMod 2) W)ˣ, CFSG.IsQuasisimple L₁ ∧
        (CFSG.QuasithinUnique.Setup.SL2Modules.repOfSubgroup L₁).IsIrreducible ∧
        B₁ ≤ normalizer (L₁ : Set (Module.End (ZMod 2) W)ˣ) ∧ B₁ ≠ ⊥ ∧
        CFSG.IsElementaryAbelian 2 B₁ ∧
        (∀ a ∈ B₁, ∀ b ∈ B₁, ∀ w : W, (b.val - 1) ((a.val - 1) w) = 0) ∧
        Nat.card W ≤ Nat.card B₁ * Nat.card {w : W // ∀ b ∈ B₁, b.val w = w} ∧
        Nonempty ((L₁ ⧸ center L₁) ≃*
          ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)))

end CFSG.Quasithin.H13.NQBlock

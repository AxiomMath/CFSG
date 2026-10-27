module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Vol2.Ch10StatementsA
public import CFSG.Quasithin.Vol2.Ch3Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def Obl10_2_3B0K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    ∀ n, Case10_1_1One T L I n →
    ∀ H : Subgroup G, IsHStar T (fsuM T L) H → 1 < E1.nParam H →
      ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ →
    ∀ (K : Subgroup G) (m : ℕ), K ∈ cComp H → oTwoUpper H = conjClosure K T →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
        Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
      B0 T L ≤ Subgroup.normalizer (K : Set G)

@[expose] def FactNatBorelFix : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)) (n : ℕ),
    BinaryNaturalSL H ⊤ ⊥ 2 n → ∀ S : Subgroup (MulAut V), IsSylowTwoOf S H →
      Nat.card ↥(fixV S) = 2 ^ n ∧
      ∀ d ∈ H ⊓ Subgroup.normalizer (S : Set (MulAut V)), d ≠ 1 → Odd (orderOf d) →
        fixV (Subgroup.zpowers d) = ⊥

@[expose] def FactTwoL2BlocksSL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L X₁ X₂ : Subgroup G) (n : ℕ), 2 ≤ n →
    SQTKGroup ↥M → IsSylowTwoOf T M → L ∈ cComp M →
    X₁ ∈ lFamily T → X₂ ∈ lFamily T → X₁ ≠ X₂ → X₁ ≤ L → X₂ ≤ L →
    (IsShort2 X₁ ∧ IsLin2Type X₁ n ∧ blockZ X₁ = ⊥ ∧ blockQ X₁ = blockU X₁) →
    (IsShort2 X₂ ∧ IsLin2Type X₂ n ∧ blockZ X₂ = ⊥ ∧ blockQ X₂ = blockU X₂) →
      IsPSL 3 2 n ↥L ∨ IsSL3 (2 ^ n) ↥L ∨
        (n = 2 ∧ IsSporadic .M23 (↥L ⧸ CFSG.pCore 2 ↥L) ∧
          CFSG.pCore 2 ↥L ≤ Subgroup.center ↥L ∧ CFSG.Open.IsQuasisimple ↥L ∧
          ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2)

@[expose] def FactRankSL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (n p : ℕ), 2 ≤ n → p.Prime → p ≠ 2 →
    p ∣ 2 ^ n - 1 → (IsPSL 3 2 n ↥L ∨ IsSL3 (2 ^ n) ↥L) →
      ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2

end CFSG.Quasithin.Vol2.Ch10.SecB

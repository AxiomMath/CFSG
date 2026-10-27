module

public import CFSG.Quasithin.Recognition.SzR1Fam
public import CFSG.Quasithin.Recognition.SzR1Gram

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def AbelStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
    (∃ n : ℕ, 2 ≤ n ∧ IsBenderQuot n (OTwoQuot K1)) →
    ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = ⊥ → False

@[expose] def NonabStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
    (∃ n : ℕ, 2 ≤ n ∧ IsBenderQuot n (OTwoQuot K1)) →
    ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ →
    IsL2Quot 2 (OTwoQuot K1) ∨ IsL2Quot 3 (OTwoQuot K1)

@[expose] def GramAbelStmt : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (Ω : Type) [Fintype Ω] (z : P) (w : Ω → P),
    SzR1.GramRel z w → z ≠ 1 → Odd (Fintype.card Ω) →
    Subgroup.closure (insert z (Set.range w)) = ⊤ →
    ∀ A : Subgroup P, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      2 ^ (Fintype.card Ω / 2) * Nat.card A ≤ Nat.card P

@[expose] def FamStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
    ∀ n : ℕ, 2 ≤ n → IsBenderQuot n (OTwoQuot K1) →
    ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ →
    ∃ (Ω : Type) (_ : Fintype Ω) (_ : SzR1.FamCtx K1 L2 S Zs Ω), Odd (Fintype.card Ω) ∧
      (IsL2Quot n (OTwoQuot K1) → Fintype.card Ω = 2 ^ n + 1) ∧
      (¬ IsL2Quot n (OTwoQuot K1) → (2 ^ n) ^ 2 + 1 ≤ Fintype.card Ω)

@[expose] def AbelIndexStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
    (∃ n : ℕ, 2 ≤ n ∧ IsBenderQuot n (OTwoQuot K1)) →
    ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ →
    ∃ A : Subgroup G, A ≤ vBeta K1 L2 S Zs ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      ∃ E : Subgroup (MulAut (OTwoQuot K1)), (∀ x ∈ E, x * x = 1) ∧
        Nat.card (vBeta K1 L2 S Zs) ≤ 2 * Nat.card E * Nat.card A

@[expose] def AutBoundStmt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → IsBenderQuot n X →
    ∀ E : Subgroup (MulAut X), (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 2 ^ (n + 1)

end CFSG.Quasithin.Background.Harris.R1

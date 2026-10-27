module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillDefs

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.TwE6RootKill


@[expose] def SubfieldLangDatumFive : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ q + 1 →
    ∀ A : Subgroup (ModGL TwistTag.E6.tag K), A ≤ twistedE6InndiagGL K σ → IsElemAbelian p A →
      p ^ 4 ≤ Nat.card A → ∃ D : TwLangData K σ q A, D.c = 1 ∧
        ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, D.v • permLattice TwistTag.E6.perm γ = -γ

@[expose] def SubfieldLangDatumThree : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → ringChar K = 2 → 3 ∣ q + 1 →
    ∀ A : Subgroup (ModGL TwistTag.E6.tag K), A ≤ twistedE6InndiagGL K σ → IsElemAbelian 3 A →
      3 ^ 5 ≤ Nat.card A → ∃ D : TwLangData K σ q A, D.c = 1

@[expose] def SubfieldLangDatumThreeFour : Prop :=
  ∀ (K₀ K : Type) [Field K₀] [Finite K₀] [Field K] [Finite K] (ι : K₀ →+* K) (σ₀ : K₀ ≃+* K₀)
    (σ : K ≃+* K) (q₀ : ℕ), Nat.card K₀ = q₀ ^ 2 → Nat.card K = (q₀ ^ 3) ^ 2 →
    (∀ c, σ₀ c = c ^ q₀) → (∀ c, σ c = c ^ q₀ ^ 3) → ringChar K₀ = 2 → 3 ∣ q₀ + 1 →
    ∀ A₀ : Subgroup (ModGL TwistTag.E6.tag K₀), A₀ ≤ twistedE6InndiagGL K₀ σ₀ →
      IsElemAbelian 3 A₀ → Nat.card A₀ = 3 ^ 4 → TwNormTwo K σ (A₀.map (baseChangeGL ι)) →
        ∃ D : TwLangData K₀ σ₀ q₀ A₀, D.c = 1

end CFSG.StandardType.TwE6FieldCore

end

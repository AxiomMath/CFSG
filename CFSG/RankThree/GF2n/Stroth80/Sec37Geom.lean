module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def Stroth37CommutingStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G)
    (_hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    IsTIMod M Q (LB M Q B) →
    ∀ m ∈ M, (∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) → conjSubgroup m B ≤ B ⊔ Z

@[expose] def Geom37Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (_hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    (∀ m ∈ M, (∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) → conjSubgroup m B ≤ B ⊔ Z) →
    n = 4 ∧ ∃ k : ℕ, Nat.card Z = 2 ^ k ∧
      IsSimpleGroup ↥(bar M Q (Lgen M (LB M Q B))) ∧
      Nonempty (↥(bar M Q (Lgen M (LB M Q B))) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (k * 3)))

@[expose] def Bridge37Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (_hc : Ctx M Q Z B) (K : Type) [Field K] [Finite K] (γ : G → K)
    (M₀ : Tim79.QuadModel Q Z K γ)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)), (∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) →
    Nonempty (↥(bar M Q (Lgen M (LB M Q B))) ≃*
      ↥(Subgroup.closure {T : M₀.E ≃ₗ[K] M₀.E | ∃ m ∈ M, ∃ x : H0 M Z,
        (x : G) ∈ conjSubgroup m (LB M Q B) ∧ φ x = T}))

end CFSG.RankThree.GF2n.Stroth80

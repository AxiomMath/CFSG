module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context
public import CFSG.Quasithin.Background.F1Hyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def IsRankOneField (X : Type) [Group X] (f : ℕ) : Prop :=
  Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) ∨
    ∃ a : ℕ, f = 2 * a + 1 ∧ Nonempty (X ≃* ↥(CFSG.Open.Sz a))

@[expose] def KL2BorelCard : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (k : ℕ), IsL2 X k → ∀ S : Sylow 2 X,
    Nat.card (S : Subgroup X) = 2 ^ k ∧
      Nat.card (Subgroup.normalizer ((S : Subgroup X) : Set X)) = 2 ^ k * (2 ^ k - 1)

@[expose] def KL2BorelComm : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (k : ℕ), IsL2 X k → ∀ S : Sylow 2 X,
    ∀ x ∈ Subgroup.normalizer ((S : Subgroup X) : Set X),
    ∀ y ∈ Subgroup.normalizer ((S : Subgroup X) : Set X),
      x * y * x⁻¹ * y⁻¹ ∈ (S : Subgroup X)

@[expose] def D2337 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z →
    ∀ K ∈ calC D.M, (K.subgroupOf D.M).Normal →
      ∀ e m : ℕ, 2 ≤ m → IsL2 (Bar2 K) (2 ^ e * m) →
      ∀ A₀ : Subgroup G, A₀ ≤ K ⊓ Subgroup.normalizer (D.T : Set G) →
        Nat.card A₀ = 2 ^ m - 1 →
        CFSG.Quasithin.borelOf K D.T ≤ c.N

end CFSG.LocalAnalysis.UniquenessCase.UC22
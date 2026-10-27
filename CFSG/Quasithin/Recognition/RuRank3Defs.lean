module

public import CFSG.Open.Catalog
public import CFSG.Sporadic.Schreier.TitsCert

public section

namespace CFSG.Quasithin.RuRank3

open scoped MatrixGroups

theorem fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

attribute [local instance] fact_prime_five

@[expose] def IsL225Plus (X : Type*) [Group X] : Prop :=
  ∃ K : Subgroup X, K.Normal ∧ K.index = 2 ∧ Nonempty (K ≃* PSL(2, GaloisField 5 2)) ∧
    Subgroup.centralizer (K : Set X) = ⊥ ∧
    ∀ S : Sylow 2 X, Nonempty (CFSG.Open.SemidihedralGroup 4 ≃* S)

@[expose] def IsSylowTwoParabolic {F : Type*} [Group F] (P : Subgroup F) : Prop :=
  ∃ S : Sylow 2 F, Subgroup.normalizer ((S : Subgroup F) : Set F) ≤ P

structure IsRudvalisRank3 (G Ω : Type*) [Group G] [MulAction G Ω] : Prop where
  faithful : FaithfulSMul G Ω
  nonempty : Nonempty Ω
  transitive : MulAction.IsPretransitive G Ω
  rank_three : ∀ ω : Ω, Nat.card (MulAction.orbitRel.Quotient (MulAction.stabilizer G ω) Ω) = 3
  twoF4 : ∀ ω : Ω, Nonempty (MulAction.stabilizer G ω ≃* CFSG.Sporadic.Schreier.Tits.titsA)
  parabolic : ∀ ω : Ω, ∃ δ : Ω,
    Nat.card (MulAction.stabilizer (MulAction.stabilizer G ω) δ) = 2 ^ 12 * 5 ∧
      IsSylowTwoParabolic (MulAction.stabilizer (MulAction.stabilizer G ω) δ)
  l225 : ∀ ω : Ω, ∃ γ : Ω, IsL225Plus (MulAction.stabilizer (MulAction.stabilizer G ω) γ)

end CFSG.Quasithin.RuRank3

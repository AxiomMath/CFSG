module

public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def KF138TrialityPGUCent :
    Prop :=
  ∀ (n : ℕ), Odd n → 1 < n → ¬ 3 ∣ n →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ n) →
    ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), α ^ 3 = 1 →
      KFacts.trialityHasKind σ α .graphField →
    ∀ Y : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), (∀ y ∈ Y, α y = y) →
      (Y.subgroupOf (autFix α)).IsSubnormal → Group.IsPerfect Y →
    ∀ π : Y →* projSU 3 2 n, Function.Surjective π → Nat.Coprime (Nat.card π.ker) 3 →
      ∃ (u : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (d t w : Y), α u = u ∧ u ^ 3 = 1 ∧
        d ^ 3 = 1 ∧ t ^ 2 = 1 ∧
        u * (d : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = d * u ∧
        u * (t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = t * u ∧
        u ∈ Subgroup.normalizer (Y : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
        π (d * t) ≠ π (t * d) ∧
        ∀ w' : Y, (w' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = u * w * u⁻¹ →
          π w' ≠ π w

end CFSG.RankThree.PartTwo.Sec4.Ronan148L

end

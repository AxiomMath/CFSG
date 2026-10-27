module

public import CFSG.LieType.Ree.FixedSubgroupData

public section

namespace CFSG.RankThree.PartOne.SEITZQ1

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

@[expose] def Phi2Ambient
    (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime] :
    Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ 2 ^ (2 * m + 1) + 1 →
    ∃ E : Subgroup (ModGL F4.tag K), E ≤ F4.reeGamma K m ∧ (∀ x ∈ E, x ^ p = 1) ∧
      Nat.card E = p ^ 2 ∧
      Subgroup.closure {k | k ∈ F4.reeGamma K m ∧ ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} =
        F4.reeGamma K m

end CFSG.RankThree.PartOne.SEITZQ1

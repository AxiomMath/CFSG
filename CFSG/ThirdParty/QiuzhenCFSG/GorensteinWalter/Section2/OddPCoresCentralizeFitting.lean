module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

namespace CFSG
end CFSG
open CFSG

/-!
# Odd prime cores centralize the Fitting subgroup when the two-core is trivial

This is the final elementary Fitting-decomposition step needed after the
source's claim that the distinguished involution centralizes every invariant
odd `p`-subgroup.
-/

namespace CFSG.GorensteinWalter

universe u

/-- If `O₂(G)=1` and `t` centralizes every odd prime core of `G`, then `t`
centralizes the full Fitting subgroup. -/
public theorem mem_centralizer_fittingSubgroupOf_of_mem_centralizer_odd_qCores_of_twoCoreOf_eq_bot
    {G : Type u} [Group G] [Finite G]
    (B : Subgroup G) (t : G) (hO2 : twoCoreOf B = ⊥)
    (hodd : ∀ p : ℕ, p.Prime → Odd p →
      t ∈ Subgroup.centralizer (qCoreOf B p : Set G)) :
    t ∈ Subgroup.centralizer (fittingSubgroupOf B : Set G) := by
  let T : Subgroup G := Subgroup.zpowers t
  have hT : T ≤ Subgroup.centralizer (fittingSubgroupOf B : Set G) := by
    rw [fittingSubgroupOf_eq_iSup_qCoreOf B]
    exact subgroup_le_centralizer_iSup_of_le_centralizer
      (P := T) (fun q : (Nat.card B).primeFactors.attach => qCoreOf B q.1.1) (by
      intro q
      apply Subgroup.zpowers_le.mpr
      by_cases hq2 : q.1.1 = 2
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hybot : y ∈ (⊥ : Subgroup G) := by
          rw [← hO2]
          simpa [qCoreOf, twoCoreOf, hq2] using hy
        rw [Subgroup.mem_bot.mp hybot]
        simp
      · have hqprime : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
        exact hodd q.1.1 hqprime (hqprime.odd_of_ne_two hq2))
  exact hT (Subgroup.mem_zpowers t)

end CFSG.GorensteinWalter

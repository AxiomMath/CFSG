module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountData
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! The numerical part of restriction (7): once its subgroup hypotheses are
available, a contributing coset is forced to have exactly four involutions. -/

public theorem firstCase_klein_restrictionSeven_fiber_eq_four
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (h7 : ∀ (n : ℕ) (y : G) (X : Subgroup G),
      4 ≤ n → y ∈ firstCaseJ c n → X ≠ ⊥ → X ≤ c.Hhat →
      Nat.Coprime 2 (Nat.card X) →
      (∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y) →
      Even (Nat.card (Subgroup.centralizer (X : Set G))) →
      Even (Nat.card ((Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G))) →
      Nat.card c.U = Nat.card X ∧ Nat.card X = 3 ∧ n = 4 ∧
        (let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
         let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
         (N.subgroupOf D).index = 6))
    {n : ℕ} {y : G} {X : Subgroup G}
    (hn : 4 ≤ n)
    (hyJ : y ∈ firstCaseJ c n) (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXodd : Nat.Coprime 2 (Nat.card X))
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y)
    (hC_even : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hN_even : Even (Nat.card
      ((Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G)))) :
    n = 4 := by
  exact (h7 n y X hn hyJ hXne hXle hXodd hXinv hC_even hN_even).2.2.1

end CFSG.GorensteinWalter

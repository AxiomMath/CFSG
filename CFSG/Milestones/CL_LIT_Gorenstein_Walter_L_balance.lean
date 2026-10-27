module

public import CFSG.Yardstones.Md42047359a2a.MilestoneProof

public section

universe u v w

namespace CFSG.Open

theorem _root_.CFSG.Milestones.cl_lit_gorenstein_walter_l_balance
    (X : Type) [Group X] [Finite X] (hK : lBalanceIsKGroup X)
    (p : ℕ) (hp : p.Prime) (P : Subgroup X) (hP : IsPGroup p P) :
    lBalancePLayer p (Subgroup.normalizer (P : Set X)) ≤ lBalancePLayer p ⊤ ∧
    lBalancePLayer p (Subgroup.centralizer (P : Set X)) ≤ lBalancePLayer p ⊤ ∧
    (lBalancePrimeCore p (⊤ : Subgroup X) = ⊥ →
      ∀ a ∈ lBalancePLayer p (Subgroup.normalizer (P : Set X)),
        ∀ b ∈ lBalancePrimeCore p (Subgroup.normalizer (P : Set X)), a * b = b * a) :=
  CFSG.Yardstones.Md42047359a2a.lBalance_of_goals X hK p hp P hP

end CFSG.Open

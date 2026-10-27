module

public import CFSG.Permutation.FiveTransitive.PrimePowerIntoSylow

public section

namespace CFSG

namespace FiveTransitive.FixedBaseInvolutionFusion

open MulAction

theorem exists_conjugate_eq
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (k : ℕ) (hk : IsMultiplyPretransitive G X k) (s : Set X) (hs : s.ncard = k)
    (S : Sylow 2 (fixingSubgroup G s)) (hS : Nat.card S = 2)
    (q : S) (hq : q ≠ 1) (g : G) (hg : orderOf g = 2)
    (hfix : k ≤ (fixedBy X g).ncard) :
    ∃ c : G, c * g * c⁻¹ = ((q : fixingSubgroup G s) : G) := by
  obtain ⟨c, u, hu⟩ := PrimePowerIntoSylow.exists_conjugate_into_set_sylow
    G X k hk s hs S g 1 (by simpa only [pow_one] using hg) hfix
  have hg1 : g ≠ 1 := by
    intro h
    simp only [h, orderOf_one] at hg
    contradiction
  have hu1 : u ≠ 1 := by
    intro h
    have hconj : c * g * c⁻¹ = 1 := hu.trans (by simp only [h, OneMemClass.coe_one])
    have hcg : c * g = c * 1 := by
      simpa only [one_mul, mul_one] using mul_inv_eq_iff_eq_mul.mp hconj
    exact hg1 (mul_left_cancel hcg)
  obtain ⟨v, hv, hvuniq⟩ := (Nat.card_eq_two_iff' (1 : S)).mp hS
  have huq : u = q := (hvuniq u hu1).trans (hvuniq q hq).symm
  exact ⟨c, hu.trans (congrArg (fun x : S => ((x : fixingSubgroup G s) : G)) huq)⟩

end FiveTransitive.FixedBaseInvolutionFusion

end CFSG

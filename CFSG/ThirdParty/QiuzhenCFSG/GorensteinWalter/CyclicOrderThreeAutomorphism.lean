module


public import Mathlib.GroupTheory.SpecificGroups.Cyclic

import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Automorphisms of a cyclic group of order three
-/

namespace CFSG.GorensteinWalter

universe u

/-- Every automorphism of a group of order three is either the identity or
inversion. -/
public theorem mulAut_eq_one_or_apply_eq_inv_of_card_eq_three
    {C : Type u} [Group C] [Finite C]
    (hcard : Nat.card C = 3) (alpha : MulAut C) :
    alpha = 1 ∨ ∀ x : C, alpha x = x⁻¹ := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclic C := isCyclic_of_prime_card hcard
  let : IsMulCommutative C := IsCyclic.isMulCommutative
  let : CommGroup C := IsMulCommutative.instCommGroup
  let invAut : MulAut C :=
    { toFun := fun x => x⁻¹
      invFun := fun x => x⁻¹
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      map_mul' := fun x y => by simp [mul_comm] }
  have hcardAut : Nat.card (MulAut C) = 2 := by
    rw [IsCyclic.card_mulAut, hcard]
    decide
  have hinvNe : invAut ≠ (1 : MulAut C) := by
    obtain ⟨z, hzOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := C) 3 (by rw [hcard])
    intro hinv
    have hzinv : z⁻¹ = z := by
      calc
        z⁻¹ = invAut z := rfl
        _ = (1 : MulAut C) z := by rw [hinv]
        _ = z := rfl
    have hzsq : z ^ 2 = 1 := by
      calc
        z ^ 2 = z * z := pow_two z
        _ = z⁻¹ * z := congrArg (fun w => w * z) hzinv.symm
        _ = 1 := by simp
    have hdvd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hzsq
    rw [hzOrder] at hdvd
    norm_num at hdvd
  obtain ⟨beta, _hbetaNe, hbetaUnique⟩ :=
    (Nat.card_eq_two_iff' (1 : MulAut C)).mp hcardAut
  have hbetaInv : beta = invAut := (hbetaUnique invAut hinvNe).symm
  by_cases halpha : alpha = 1
  · exact Or.inl halpha
  · right
    have halphaInv : alpha = invAut :=
      (hbetaUnique alpha halpha).trans hbetaInv
    intro x
    rw [halphaInv]
    rfl

end CFSG.GorensteinWalter

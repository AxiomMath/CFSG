module

public import CFSG.Permutation.FiveTransitive.Reduction
public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.PCycleJordan

public section

namespace CFSG

namespace FiveTransitive.PrimePredFour

private theorem alternatingGroup_le_of_prime_dvd_descFactorial
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    {p : ℕ} (hp : p.Prime)
    (hpdiv : p ∣ (Fintype.card X).descFactorial 5)
    (hsmall : Fintype.card X < 2 * p)
    (hfixed : p + 3 ≤ Fintype.card X) :
    alternatingGroup X ≤ P := by
  classical
  have hdegree : 5 ≤ Fintype.card X := by omega
  have hpCard : p ∣ Nat.card P :=
    hpdiv.trans
      (FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive
        P X 5 hdegree h5)
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := P) p hpCard
  have huPerm : orderOf (u : Equiv.Perm X) = p := by
    rw [Subgroup.orderOf_coe, hu]
  have hcycle : (u : Equiv.Perm X).IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by rw [huPerm]; exact hp)
      (by rw [huPerm]; exact hsmall)
  have hsupport : (u : Equiv.Perm X).support.card = p := by
    rw [← hcycle.orderOf, huPerm]
  let _ : MulAction.IsMultiplyPretransitive P X 5 := h5
  have h2 : MulAction.IsMultiplyPretransitive P X 2 :=
    MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 2) (n := 5) (by omega)
      (by simpa only [Nat.card_eq_fintype_card] using hdegree)
  have hprimitive : MulAction.IsPreprimitive P X :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2
  exact OddOrder.Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
    hprimitive hp (by simpa only [Nat.card_eq_fintype_card] using hfixed)
    hcycle hsupport u.property

theorem alternatingGroup_le_of_sub_four_prime
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hdegree : 9 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (hprime : (Fintype.card X - 4).Prime) :
    alternatingGroup X ≤ P := by
  apply alternatingGroup_le_of_prime_dvd_descFactorial X P h5 hprime
  · simp only [Nat.descFactorial, Nat.sub_zero, mul_one]
    exact dvd_mul_right _ _
  · omega
  · omega

theorem alternatingGroup_le_of_sub_three_prime
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hdegree : 8 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (hprime : (Fintype.card X - 3).Prime) :
    alternatingGroup X ≤ P := by
  apply alternatingGroup_le_of_prime_dvd_descFactorial X P h5 hprime
  · simp only [Nat.descFactorial, Nat.sub_zero, mul_one]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  · omega
  · omega

end FiveTransitive.PrimePredFour

end CFSG

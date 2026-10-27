module

public import CFSG.GroupTheory.SolvableHallNodes
public import Mathlib.GroupTheory.Nilpotent

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime

universe u v

theorem two_subgroup_solvable_coprime
    {M : Type u} [Group M] [Finite M] {A : Type v} [Group A] [Finite A]
    (hM : IsPGroup 2 M) (hA : Odd (Nat.card A)) (Q : Subgroup M) :
    Group.IsSolvable Q ∧ Nat.Coprime (Nat.card A) (Nat.card Q) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 Q := hM.to_subgroup Q
  let : Group.IsNilpotent Q := hQ.isNilpotent
  refine ⟨inferInstance, ?_⟩
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  rw [hn]
  exact hA.coprime_two_right.pow_right n

theorem two_group_solvable_coprime
    {M : Type u} [Group M] [Finite M] {A : Type v} [Group A] [Finite A]
    (hM : IsPGroup 2 M) (hA : Odd (Nat.card A)) :
    Group.IsSolvable M ∧ Nat.Coprime (Nat.card A) (Nat.card M) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsNilpotent M := hM.isNilpotent
  refine ⟨inferInstance, ?_⟩
  obtain ⟨n, hn⟩ := hM.exists_card_eq
  rw [hn]
  exact hA.coprime_two_right.pow_right n

theorem fixedPointSubgroup_eq_bot_of_involution_capture
    {M : Type u} [Group M] [Finite M] {A : Type v} [Group A]
    [MulDistribMulAction A M] (hM : IsPGroup 2 M) (Q : Subgroup M)
    (hInv : ∀ x : M, orderOf x = 2 → x ∈ Q)
    (hQfix : ∀ x : M, x ∈ Q → (∀ a : A, a • x = x) → x = 1) :
    CFSG.fixedPointSubgroup A M = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  let C := CFSG.fixedPointSubgroup A M
  have hC : IsPGroup 2 C := hM.to_subgroup C
  have hcard : Nat.card C ≠ 1 := by
    intro hcard
    exact hne (Subgroup.card_eq_one.mp hcard)
  have hdvd : 2 ∣ Nat.card C := hC.card_eq_or_dvd.resolve_left hcard
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hdvd
  have hxM : orderOf (x : M) = 2 := by
    simpa only [orderOf_submonoid] using hx
  have hxone : (x : M) = 1 := hQfix x (hInv x hxM) x.property
  have hxoneC : x = 1 := Subtype.ext hxone
  rw [hxoneC, orderOf_one] at hx
  omega

theorem fixedPointSubgroup_and_quotient_eq_bot_of_involution_capture
    {M : Type u} [Group M] [Finite M] {A : Type v} [Group A] [Finite A]
    [MulDistribMulAction A M] (hM : IsPGroup 2 M) (hA : Odd (Nat.card A))
    (Q : Subgroup M) [Q.Normal] (hQinv : CFSG.IsInvariant A M Q)
    (hInv : ∀ x : M, orderOf x = 2 → x ∈ Q)
    (hQfix : ∀ x : M, x ∈ Q → (∀ a : A, a • x = x) → x = 1) :
    letI : MulDistribMulAction A (M ⧸ Q) :=
      CFSG.quotientMulDistribMulAction (A := A) (G := M) Q hQinv
    CFSG.fixedPointSubgroup A M = ⊥ ∧ CFSG.fixedPointSubgroup A (M ⧸ Q) = ⊥ := by
  let : MulDistribMulAction A (M ⧸ Q) :=
    CFSG.quotientMulDistribMulAction (A := A) (G := M) Q hQinv
  have hfixed : CFSG.fixedPointSubgroup A M = ⊥ :=
    fixedPointSubgroup_eq_bot_of_involution_capture hM Q hInv hQfix
  obtain ⟨hQsolv, hQcop⟩ := two_subgroup_solvable_coprime hM hA Q
  have hlift := CFSG.SolvableHall.coprime_solvable_kernel_fixed_point_lifting
    Q hQinv hQsolv hQcop
  exact ⟨hfixed, by simpa only [hfixed, Subgroup.map_bot] using hlift⟩

theorem fixedPointSubgroup_and_quotient_eq_bot_of_restricted_fixed_eq_bot
    {M : Type u} [Group M] [Finite M] {A : Type v} [Group A] [Finite A]
    [MulDistribMulAction A M] (hM : IsPGroup 2 M) (hA : Odd (Nat.card A))
    (Q : Subgroup M) [Q.Normal] [hQinv : CFSG.IsInvariant A M Q]
    (hInv : ∀ x : M, orderOf x = 2 → x ∈ Q)
    (hQfixed : CFSG.fixedPointSubgroup A Q = ⊥) :
    letI : MulDistribMulAction A (M ⧸ Q) :=
      CFSG.quotientMulDistribMulAction (A := A) (G := M) Q hQinv
    CFSG.fixedPointSubgroup A M = ⊥ ∧ CFSG.fixedPointSubgroup A (M ⧸ Q) = ⊥ := by
  apply fixedPointSubgroup_and_quotient_eq_bot_of_involution_capture hM hA Q hQinv hInv
  intro x hx hfix
  have hxfix : (⟨x, hx⟩ : Q) ∈ CFSG.fixedPointSubgroup A Q := by
    intro a
    exact Subtype.ext (hfix a)
  rw [hQfixed] at hxfix
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hxfix)

end CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime

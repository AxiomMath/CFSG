module

public import CFSG.Sporadic.Bridge.Converse
public import CFSG.RankThree.OddKernel.SporadicKernelRestrictionB
public import CFSG.RankThree.PartOne.CTP.SporadicOrders
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.CarrierPerfect

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.Open (MonsterY443Derived monsterOrder)

theorem not_prime_of_even_gt_two {n : ℕ} (h2 : 2 ∣ n) (hn : 2 < n) : ¬ n.Prime := fun hp => by
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega

theorem not_prime_card_of_even_gt_two {X : Type} [Group X] {n : ℕ} (h : Nat.card X = n)
    (h2 : 2 ∣ n) (hn : 2 < n) : ¬ (Nat.card X).Prime := by
  rw [h]
  exact not_prime_of_even_gt_two h2 hn

section M23Card

theorem card_carrier_M23 : Nat.card (Carrier .M23) = 10200960 := by
  have h : Nat.card (Carrier .M23) = Nat.card CFSG.M23.M23Group.H0 := by
    show Nat.card (CFSG.Blueprint.NativeSporadic.M23) = _
    rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  have hH := CFSG.M23.M23Group.card_M23
  rw [Fintype.card_eq_nat_card] at hH
  rw [h]
  exact hH

end M23Card

theorem carrier_M_finite_isPerfect (hcard : Nat.card MonsterY443Derived = monsterOrder)
    (hsimple : IsSimpleGroup MonsterY443Derived) :
    Finite (Carrier .M) ∧ Group.IsPerfect (Carrier .M) := by
  obtain ⟨hfin, hsim⟩ := CFSG.Sporadic.Bridge.carrier_M_finite_simple hcard hsimple
  have : IsSimpleGroup (Carrier .M) := hsim
  have hc : Nat.card (Carrier .M) = monsterOrder :=
    (Nat.card_congr CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.toEquiv).trans hcard
  exact ⟨hfin, isPerfect_of_simple_not_prime_card (Carrier .M)
    (not_prime_card_of_even_gt_two hc (by norm_num [monsterOrder])
      (by norm_num [monsterOrder]))⟩

theorem carrier_card_not_prime_of_ne_M (s : TauCeti.SporadicName) (hs : s ≠ .M) :
    ¬ (Nat.card (Carrier s)).Prime := by
  cases s with
  | M11 =>
    exact not_prime_card_of_even_gt_two CFSG.Sporadic.Mathieu.card_M11 (by norm_num) (by norm_num)
  | M12 =>
    exact not_prime_card_of_even_gt_two CFSG.Sporadic.Mathieu.card_M12 (by norm_num) (by norm_num)
  | M22 =>
    exact not_prime_card_of_even_gt_two CFSG.Sporadic.Mathieu.card_M22 (by norm_num) (by norm_num)
  | M23 => exact not_prime_card_of_even_gt_two card_carrier_M23 (by norm_num) (by norm_num)
  | M24 =>
    exact not_prime_card_of_even_gt_two CFSG.Sporadic.Mathieu.card_M24 (by norm_num) (by norm_num)
  | J1 => exact not_prime_card_of_even_gt_two CFSG.Sporadic.J1.card_J1 (by norm_num) (by norm_num)
  | J2 => exact not_prime_card_of_even_gt_two CFSG.Sporadic.J2.card_J2 (by norm_num) (by norm_num)
  | J3 => exact not_prime_card_of_even_gt_two CFSG.Sporadic.J3.card_J3 (by norm_num) (by norm_num)
  | J4 => exact not_prime_card_of_even_gt_two CFSG.Sporadic.J4.card_J4 (by norm_num) (by norm_num)
  | HS => exact not_prime_card_of_even_gt_two CFSG.Sporadic.HS.card_HS (by norm_num) (by norm_num)
  | McL =>
    exact not_prime_card_of_even_gt_two CFSG.Sporadic.McL.card_McL (by norm_num) (by norm_num)
  | He => exact not_prime_card_of_even_gt_two CFSG.Sporadic.He.card_He (by norm_num) (by norm_num)
  | Ru => exact not_prime_card_of_even_gt_two CFSG.Sporadic.Ru.card_Ru (by norm_num) (by norm_num)
  | Suz =>
    exact not_prime_card_of_even_gt_two CFSG.Sporadic.Suz.card_Suz (by norm_num) (by norm_num)
  | ONan => exact not_prime_card_of_even_gt_two CFSG.Sporadic.ON.card_ON (by norm_num) (by norm_num)
  | Co1 =>
    exact not_prime_card_of_even_gt_two CFSG.Sporadic.Co1.card_Co1 (by norm_num) (by norm_num)
  | Co2 =>
    exact not_prime_card_of_even_gt_two CFSG.Sporadic.Co2.card_Co2 (by norm_num) (by norm_num)
  | Co3 =>
    exact not_prime_card_of_even_gt_two CFSG.Sporadic.Co3.card_Co3 (by norm_num) (by norm_num)
  | Fi22 =>
    exact not_prime_card_of_even_gt_two CFSG.Sporadic.Fi22.card_Fi22 (by norm_num) (by norm_num)
  | Fi23 =>
    exact not_prime_card_of_even_gt_two CFSG.Sporadic.Fi23.card_Fi23 (by norm_num) (by norm_num)
  | Fi24Prime =>
    exact not_prime_card_of_even_gt_two CFSG.Sporadic.Fi24.card_Fi24prime
      (by norm_num) (by norm_num)
  | HN => exact not_prime_card_of_even_gt_two CFSG.Sporadic.HN.card_HN (by norm_num) (by norm_num)
  | Ly => exact not_prime_card_of_even_gt_two CFSG.Sporadic.Ly.card_Ly (by norm_num) (by norm_num)
  | Th =>
    exact not_prime_card_of_even_gt_two CFSG.RankThree.PartOne.CTP.card_Th
      (by norm_num) (by norm_num)
  | B =>
    exact not_prime_card_of_even_gt_two CFSG.RankThree.OddKernel.card_B_eq
      (by norm_num) (by norm_num)
  | M => exact absurd rfl hs

theorem carrier_finite_isPerfect_of_ne_M (s : TauCeti.SporadicName) (hs : s ≠ .M) :
    Finite (Carrier s) ∧ Group.IsPerfect (Carrier s) := by
  obtain ⟨hfin, hsim⟩ := CFSG.Sporadic.Bridge.carrier_finite_simple_of_ne_M s hs
  have : IsSimpleGroup (Carrier s) := hsim
  exact ⟨hfin, isPerfect_of_simple_not_prime_card (Carrier s)
    (carrier_card_not_prime_of_ne_M s hs)⟩

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

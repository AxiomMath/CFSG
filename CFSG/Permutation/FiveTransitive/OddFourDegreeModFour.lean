module

public import CFSG.Permutation.FiveTransitive.HallInvolutionConsequence

public section

namespace CFSG

namespace FiveTransitive.OddFourDegreeModFour

open MulAction
open Research.HallInvolutionConsequence
open Research.OddFourCentralizer

private theorem involution_fixed_card_two
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hn : 8 ≤ Fintype.card X) (hdiv : 4 ∣ Fintype.card X)
    (e : Fin 4 ↪ X) (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (s : G) (hs : s ^ 2 = 1) (hsne : s ≠ 1) :
    (fixedBy X s).ncard = 2 := by
  classical
  have hcases := involution_fixedBy_ncard_eq_two_or_three h4 hn e hodd s hs hsne
  rcases hcases with htwo | hthree
  · exact htwo
  let σ := MulAction.toPermHom G X s
  have hσ : σ ^ 2 = 1 := by
    change (MulAction.toPermHom G X s)^2 = 1
    rw [← map_pow, hs, map_one]
  have heven : 2 ∣ σ.support.card := Equiv.Perm.two_dvd_card_support hσ
  have hfix : (fixedBy X s).ncard = Fintype.card X - σ.support.card := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card (Function.fixedPoints σ) = _
    rw [Nat.card_eq_fintype_card, Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType]
  obtain ⟨k, hk⟩ := hdiv
  obtain ⟨j, hj⟩ := heven
  have hle : σ.support.card ≤ Fintype.card X := Finset.card_le_univ _
  omega

theorem not_four_dvd_degree
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hn : 8 ≤ Fintype.card X)
    (e : Fin 4 ↪ X) (hodd : Odd (Nat.card (MulAction.stabilizer G e))) :
    ¬ 4 ∣ Fintype.card X := by
  classical
  intro hdiv
  obtain ⟨s, d, hs, hsne, hd, hsbase, hdbase⟩ :=
    exists_single_double_involution_lifts h4 e hodd
  have hfix := involution_fixed_card_two G X h4 hn hdiv e hodd s hs hsne
  have heq := single_double_centralizer_equation_of_odd_stabilizer
    h4 hn e hodd s d hs hd hsne hsbase hdbase
  have hoddA : Odd (Nat.card (centralizingBaseStabilizer e s)) := by
    apply hodd.of_dvd_nat
    exact Subgroup.card_dvd_of_le (show centralizingBaseStabilizer e s ≤
      MulAction.stabilizer G e from inf_le_left)
  let a := Nat.card (centralizingBaseStabilizer e s)
  let b := Nat.card (centralizingBaseStabilizer e d)
  simp only [hfix, show (2 : ℕ).descFactorial 2 = 2 by decide, Nat.sub_sub] at heq
  have heq' : 2 * a = (Fintype.card X - 4) * b := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < Fintype.card X - 2 by omega)
    simpa only [a, b, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using heq
  obtain ⟨k, hk⟩ := hdiv
  have hn4 : Fintype.card X - 4 = 4 * (k - 1) := by omega
  rw [hn4] at heq'
  apply hoddA.not_two_dvd_nat
  refine ⟨(k - 1) * b, ?_⟩
  change a = 2 * ((k - 1) * b)
  nlinarith only [heq']

end FiveTransitive.OddFourDegreeModFour

end CFSG

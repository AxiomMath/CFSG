module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SA9Defs

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open Equiv Equiv.Perm Subgroup

private lemma natCard_centralizer_replicate_three {σ : Perm (Fin 9)} {m : ℕ} (hm : 1 ≤ m)
    (hσ : σ.cycleType = Multiset.replicate m 3) :
    Nat.card (Subgroup.centralizer {σ}) = Nat.factorial (9 - m * 3) * 3 ^ m * Nat.factorial m := by
  have h0 : m ≠ 0 := by omega
  rw [Equiv.Perm.nat_card_centralizer σ, hσ]
  simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.prod_replicate,
    Multiset.toFinset_replicate, if_neg h0, Finset.prod_singleton, Multiset.count_replicate_self,
    Fintype.card_fin]

private theorem isThreeCycle_of_orderOf_three_commute_five {σ κ : Perm (Fin 9)}
    (hσ : orderOf σ = 3) (hκ : orderOf κ = 5) (hc : Commute σ κ) : IsThreeCycle σ := by
  have hlcm : σ.cycleType.lcm = 3 := by rw [Equiv.Perm.lcm_cycleType, hσ]
  have hall : ∀ n ∈ σ.cycleType, n = 3 := by
    intro n hn
    have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    have hdvd : n ∣ 3 := by
      rw [← hlcm]
      exact Multiset.dvd_lcm hn
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · omega
    · exact h
  obtain ⟨m, hm⟩ : ∃ m, σ.cycleType = Multiset.replicate m 3 :=
    ⟨_, Multiset.eq_replicate_card.mpr hall⟩
  have hsum : m * 3 = σ.support.card := by
    have h := Equiv.Perm.sum_cycleType σ
    simp only [hm, Multiset.sum_replicate, smul_eq_mul] at h
    exact h
  have hm3 : m ≤ 3 := by
    have h := Finset.card_le_univ σ.support
    rw [Fintype.card_fin] at h
    omega
  have hm1 : 1 ≤ m := by
    by_contra h0
    have h0' : m = 0 := by omega
    subst h0'
    have h1 : σ = 1 := Equiv.Perm.cycleType_eq_zero.mp (by simpa using hm)
    subst h1
    simp at hσ
  have hmem : κ ∈ Subgroup.centralizer {σ} :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc.symm.eq
  have hκc : orderOf (⟨κ, hmem⟩ : Subgroup.centralizer {σ}) = 5 :=
    (Subgroup.orderOf_coe (⟨κ, hmem⟩ : Subgroup.centralizer {σ})).symm.trans hκ
  have hdvd : orderOf (⟨κ, hmem⟩ : Subgroup.centralizer {σ}) ∣
      Nat.card (Subgroup.centralizer {σ}) := orderOf_dvd_natCard _
  rw [hκc, natCard_centralizer_replicate_three hm1 hm] at hdvd
  interval_cases m
  · exact hm.trans (Multiset.replicate_one 3)
  · exact absurd hdvd (by decide)
  · exact absurd hdvd (by decide)

private lemma isThreeCycle_a9T0 : IsThreeCycle (a9fT0 : Perm (Fin 9)) := by
  show IsThreeCycle (List.formPerm [(0 : Fin 9), 1, 2])
  rw [← card_support_eq_three_iff,
    List.support_formPerm_of_nodup [(0 : Fin 9), 1, 2] (by decide) (by simp)]
  decide

theorem isThreeCycle_of_commute_order_five {x y : alternatingGroup (Fin 9)} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hy5 : orderOf y = 5) (hxy : x * y = y * x) :
    IsThreeCycle (x : Perm (Fin 9)) := by
  have hx3' : (x : Perm (Fin 9)) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
  have hx1' : (x : Perm (Fin 9)) ≠ 1 := fun h => hx1 (Subtype.ext (by simpa using h))
  have hord : orderOf (x : Perm (Fin 9)) = 3 := orderOf_eq_prime hx3' hx1'
  have hord' : orderOf (y : Perm (Fin 9)) = 5 := by
    rw [Subgroup.orderOf_coe]
    exact hy5
  have hc : Commute (x : Perm (Fin 9)) (y : Perm (Fin 9)) := by
    show (x : Perm (Fin 9)) * (y : Perm (Fin 9)) = (y : Perm (Fin 9)) * (x : Perm (Fin 9))
    simpa using congrArg Subtype.val hxy
  exact isThreeCycle_of_orderOf_three_commute_five hord hord' hc

theorem exists_conj_a9T0 {x : alternatingGroup (Fin 9)} (hx : IsThreeCycle (x : Perm (Fin 9))) :
    ∃ q : alternatingGroup (Fin 9), q * x * q⁻¹ = a9fT0 := by
  have h5 : 5 ≤ Nat.card (Fin 9) := by simp [Nat.card_eq_fintype_card]
  obtain ⟨q, hq⟩ := isConj_iff.mp (alternatingGroup.isThreeCycle_isConj h5 hx isThreeCycle_a9T0)
  exact ⟨q, hq⟩

end CFSG.RankThree.PartTwo.Sec8.Hering611

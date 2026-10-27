module

public import CFSG.RankThree.PartTwo.Sec15.ThmDDefs
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open Equiv Equiv.Perm

theorem card_support_cycle_of_orderOf_seven {σ : Perm (Fin 10)} (h : orderOf σ = 7) :
    σ.support.card = 7 ∧ σ.IsCycle := by
  have hl := Equiv.Perm.lcm_cycleType σ
  rw [h] at hl
  have hmem : ∀ n ∈ σ.cycleType, n = 7 := by
    intro n hn
    have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    have hd : n ∣ 7 := hl ▸ Multiset.dvd_lcm hn
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hd with h1 | h7
    · omega
    · exact h7
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 7 :=
    Multiset.eq_replicate_card.mpr hmem
  have hsum := Equiv.Perm.sum_cycleType σ
  have hle : σ.support.card ≤ 10 := by
    simpa using Finset.card_le_univ σ.support
  have hk : Multiset.card σ.cycleType = 1 := by
    have hsum' : σ.support.card = Multiset.card σ.cycleType * 7 := by
      rw [← hsum]
      have : σ.cycleType.sum = (Multiset.replicate (Multiset.card σ.cycleType) 7).sum :=
        congrArg Multiset.sum hrep
      rw [this, Multiset.sum_replicate, smul_eq_mul]
    have hk1 : Multiset.card σ.cycleType ≤ 1 := by omega
    have hk0 : Multiset.card σ.cycleType ≠ 0 := by
      intro h0
      have : σ.cycleType = 0 := Multiset.card_eq_zero.mp h0
      rw [this] at hl
      simp at hl
    omega
  refine ⟨?_, Equiv.Perm.card_cycleType_eq_one.mp hk⟩
  rw [← hsum, hrep, hk]
  simp

theorem isThreeCycle_of_commute_order_seven {σ x : Perm (Fin 10)} (hσ : orderOf σ = 7)
    (hx : orderOf x = 3) (hc : Commute x σ) : x.IsThreeCycle := by
  classical
  obtain ⟨hcard, hcyc⟩ := card_support_cycle_of_orderOf_seven hσ
  have hx3 : x ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hxne : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hxσ : ∀ z, σ (x z) = x (σ z) := fun z => by
    have := congrArg (fun f : Perm (Fin 10) => f z) hc.eq
    simpa using this.symm
  have hS : ∀ z, x z ∈ σ.support ↔ z ∈ σ.support := by
    intro z
    simp only [Equiv.Perm.mem_support]
    constructor
    · intro h h'
      apply h
      rw [hxσ, h']
    · intro h h'
      apply h
      rw [hxσ] at h'
      exact x.injective h'
  have hfix : ∃ a : {z // z ∈ σ.support}, x.subtypePerm hS a = a := by
    refine Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1) ?_ ?_
    · rw [Fintype.card_coe, hcard]
      norm_num
    · have h3 : (x.subtypePerm hS) ^ 3 = 1 := by
        rw [Equiv.Perm.subtypePerm_pow]
        ext z
        simp [Equiv.Perm.subtypePerm_apply, hx3]
      simpa using h3
  obtain ⟨a, ha⟩ := hfix
  have hax : x a = a := congrArg Subtype.val ha
  have hall : ∀ z ∈ σ.support, x z = z := by
    intro z hz
    obtain ⟨i, hi⟩ := hcyc.exists_pow_eq (Equiv.Perm.mem_support.mp a.2)
      (Equiv.Perm.mem_support.mp hz)
    rw [← hi]
    have h1 : x ((σ ^ i) a) = (σ ^ i) (x a) := by
      have := congrArg (fun f : Perm (Fin 10) => f a) (hc.zpow_right i).eq
      simpa using this
    rw [h1, hax]
  have hsub : x.support ⊆ σ.supportᶜ := by
    intro z hz
    rw [Finset.mem_compl]
    intro hzS
    exact (Equiv.Perm.mem_support.mp hz) (hall z hzS)
  have hle3 : x.support.card ≤ 3 := by
    have := Finset.card_le_card hsub
    rw [Finset.card_compl, hcard] at this
    simpa using this
  have hge : 2 ≤ x.support.card := by
    have h0 : x.support.card ≠ 0 := fun h => hxne (Equiv.Perm.card_support_eq_zero.mp h)
    have h1 : x.support.card ≠ 1 := Equiv.Perm.card_support_ne_one x
    omega
  have h2 : x.support.card ≠ 2 := by
    intro h2
    obtain ⟨u, v, -, huv⟩ := Equiv.Perm.card_support_eq_two.mp h2
    have : x ^ 2 = 1 := by
      rw [huv, sq]
      exact Equiv.swap_mul_self u v
    have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one this
    rw [hx] at hd
    omega
  exact card_support_eq_three_iff.mp (by omega)

theorem a7CentralizerThreeCycle_holds : A7CentralizerThreeCycle := by
  rintro K ⟨φ⟩ x hx hx3
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcard : 7 ∣ Nat.card (alternatingGroup (Fin 7)) := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Fintype.card_fin, Nat.factorial]
  obtain ⟨g₀, hg₀⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 7)) 7 hcard
  have hgK : ((φ.symm g₀ : ↥K) : alternatingGroup (Fin 10)) ∈ K := (φ.symm g₀).2
  have hg7 : orderOf ((φ.symm g₀ : ↥K) : alternatingGroup (Fin 10)) = 7 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hg₀]
  have hgperm : orderOf (((φ.symm g₀ : ↥K) : alternatingGroup (Fin 10)) : Perm (Fin 10)) = 7 := by
    rw [Subgroup.orderOf_coe, hg7]
  have hxperm : orderOf ((x : alternatingGroup (Fin 10)) : Perm (Fin 10)) = 3 := by
    rw [Subgroup.orderOf_coe, hx3]
  have hxc : Commute ((x : alternatingGroup (Fin 10)) : Perm (Fin 10))
      (((φ.symm g₀ : ↥K) : alternatingGroup (Fin 10)) : Perm (Fin 10)) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx _ hgK).symm
  exact isThreeCycle_of_commute_order_seven hgperm hxperm hxc

end CFSG.RankThree.PartTwo.Sec15.ThmD

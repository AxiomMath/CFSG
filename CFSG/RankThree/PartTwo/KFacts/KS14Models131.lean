module

public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG CFSG.Blueprint
open scoped commutatorElement

section Simple

variable {G : Type*} [Group G]

theorem exists_ne_comm_of_isSimpleGroup_of_not_prime [Finite G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hab
  have hcomm : ∀ a b : G, a * b = b * a := fun a b => by
    by_contra hne
    exact hab ⟨a, b, hne⟩
  have hnt : Nontrivial G := IsSimpleGroup.toNontrivial
  have h1 : Nat.card G ≠ 1 := fun h1 => by
    have := Finite.one_lt_card (α := G)
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) p hpd
  have hN : (Subgroup.zpowers g).Normal :=
    ⟨fun n hn x => by rwa [hcomm x n, mul_inv_cancel_right]⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g) with hb | ht
  · have : g = 1 := by
      rw [← Subgroup.mem_bot, ← hb]
      exact Subgroup.mem_zpowers g
    rw [this, orderOf_one] at hg
    exact hp.one_lt.ne' hg.symm
  · apply h
    rw [← Subgroup.card_top (G := G), ← ht, Nat.card_zpowers, hg]
    exact hp

theorem isPerfect_of_isSimpleGroup_of_ne_comm [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) :
    Group.IsPerfect G := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnab
    apply hxy
    have hmem : ⁅x, y⁆ ∈ commutator G := by
      rw [commutator_eq_closure]
      exact Subgroup.subset_closure (commutator_mem_commutatorSet x y)
    rw [h, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  · exact h

theorem center_eq_bot_of_isSimpleGroup_of_ne_comm [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem isPerfect_center_of_isSimpleGroup [Finite G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : Group.IsPerfect G ∧ Subgroup.center G = ⊥ :=
  ⟨isPerfect_of_isSimpleGroup_of_ne_comm (exists_ne_comm_of_isSimpleGroup_of_not_prime h),
    center_eq_bot_of_isSimpleGroup_of_ne_comm (exists_ne_comm_of_isSimpleGroup_of_not_prime h)⟩

end Simple

theorem sporadicModels131 : Sec13.SporadicModels131 := by
  obtain ⟨-, -, h22⟩ := CFSG.Sporadic.Mathieu.fam_m22_simplicity
  obtain ⟨-, -, h12⟩ := CFSG.Sporadic.Mathieu.fam_m12_simplicity
  have hJ := CFSG.Sporadic.J2.isSimpleGroup_J2
  refine ⟨isPerfect_center_of_isSimpleGroup ?_, isPerfect_center_of_isSimpleGroup ?_,
    isPerfect_center_of_isSimpleGroup ?_⟩
  · rw [CFSG.Sporadic.Mathieu.card_M22]
    norm_num
  · rw [CFSG.Sporadic.Mathieu.card_M12]
    norm_num
  · rw [CFSG.Sporadic.J2.card_J2]
    norm_num

end CFSG.RankThree.PartTwo.KFacts.KS14

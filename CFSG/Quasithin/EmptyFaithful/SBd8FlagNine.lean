module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag3

public section

namespace CFSG.Quasithin

namespace SBd8

namespace Flag

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L

section Abstract

variable {G : Type*} [Group G]

theorem nine_dvd_card_of_commute {x y : G} (hc : x * y = y * x) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hyx : y ≠ x) (hyx2 : y ≠ x ^ 2) : 9 ∣ Nat.card G := by
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  set N : Subgroup G := Subgroup.zpowers x with hN
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  have hNC : N ≤ C := (Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_iff.2 fun h hh => by
    rw [Set.mem_singleton_iff.1 hh])
  have hyC : y ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact hc
  have hyN : y ∉ N := by
    intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
    have h1 : x ^ (k % (3 : ℕ)) = y := by
      rw [← hk, ← zpow_mod_orderOf x k, hxo]
    have h2 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases h2 with h2 | h2 | h2
    · rw [Nat.cast_ofNat, h2] at h1
      exact hy1 (by rw [← h1, zpow_zero])
    · rw [Nat.cast_ofNat, h2] at h1
      exact hyx (by rw [← h1, zpow_one])
    · rw [Nat.cast_ofNat, h2] at h1
      exact hyx2 (by rw [← h1]; norm_cast)
  set N' : Subgroup C := N.subgroupOf C with hN'
  have hcent : N' ≤ Subgroup.center C := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro c
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hn)
    apply Subtype.ext
    have hxc : Commute x (c : G) := (Subgroup.mem_centralizer_iff.1 c.2) x rfl |>.symm.symm
    have : Commute (x ^ k) (c : G) := hxc.zpow_left k
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hk]
    exact this.symm.eq
  have hnormal : N'.Normal := Subgroup.normal_of_le_center hcent
  have hcardN' : Nat.card N' = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv, hN, Nat.card_zpowers, hxo]
  set yC : C := ⟨y, hyC⟩ with hyC'
  have hq3 : (QuotientGroup.mk yC : C ⧸ N') ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : yC ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, QuotientGroup.mk_one]
  have hq1 : (QuotientGroup.mk yC : C ⧸ N') ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff] at h
    exact hyN (Subgroup.mem_subgroupOf.1 h)
  have hqo : orderOf (QuotientGroup.mk yC : C ⧸ N') = 3 := orderOf_eq_prime hq3 hq1
  have hdvd : 3 ∣ Nat.card (C ⧸ N') := hqo ▸ orderOf_dvd_natCard _
  have hcard : Nat.card C = Nat.card (C ⧸ N') * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N', hcardN']
  have : 9 ∣ Nat.card C := by
    rw [hcard]
    exact (Nat.mul_dvd_mul_right hdvd 3 : 3 * 3 ∣ Nat.card (C ⧸ N') * 3)
  exact this.trans (Subgroup.card_subgroup_dvd_card C)

end Abstract

section Concrete

@[expose] def triElt (n a : ℕ) : SpecialLinearGroup (Fin n) (ZMod 2) :=
  if h : a + 2 ≤ n then
    liftT a 2 h (i := 0) (j := 1) (by decide) * liftT a 2 h (i := 1) (j := 0) (by decide)
  else 1

theorem triElt_mem {n a : ℕ} {I : Set ℕ} (h : a + 2 ≤ n) (ha : a + 1 ∉ I) :
    triElt n a ∈ flagStabilizer n (ZMod 2) I := by
  simp only [triElt, h, ↓reduceDIte]
  have hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + 2) := by
    intro c hc ⟨h1, h2⟩
    have : c = a + 1 := by omega
    exact ha (this ▸ hc)
  exact mul_mem (liftT_mem_flagStabilizer a 2 h hno _) (liftT_mem_flagStabilizer a 2 h hno _)

theorem triElt_facts {n a b : ℕ} (hab : a + 2 ≤ b) (hbn : b + 2 ≤ n) (hn : n ≤ 5) :
    triElt n a * triElt n b = triElt n b * triElt n a ∧ triElt n a ^ 3 = 1 ∧ triElt n b ^ 3 = 1 ∧
      triElt n a ≠ 1 ∧ triElt n b ≠ 1 ∧ triElt n b ≠ triElt n a ∧
      triElt n b ≠ triElt n a ^ 2 := by
  have hb3 : b ≤ 3 := by omega
  have ha1 : a ≤ 1 := by omega
  interval_cases n <;> interval_cases b <;> interval_cases a <;> first | omega | decide

theorem nine_dvd_card_flagStabilizer {n : ℕ} {I : Set ℕ} {a b : ℕ} (hab : a + 2 ≤ b)
    (hbn : b + 2 ≤ n) (hn : n ≤ 5) (ha : a + 1 ∉ I) (hb : b + 1 ∉ I) :
    9 ∣ Nat.card ↥(flagStabilizer n (ZMod 2) I) := by
  obtain ⟨hc, hx3, hy3, hx1, hy1, hyx, hyx2⟩ := triElt_facts hab hbn hn
  have hxI := triElt_mem (n := n) (a := a) (I := I) (by omega) ha
  have hyI := triElt_mem (n := n) (a := b) (I := I) hbn hb
  refine nine_dvd_card_of_commute (x := ⟨triElt n a, hxI⟩) (y := ⟨triElt n b, hyI⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Subtype.ext hc
  · exact Subtype.ext hx3
  · exact Subtype.ext hy3
  · exact fun h => hx1 (congrArg Subtype.val h)
  · exact fun h => hy1 (congrArg Subtype.val h)
  · exact fun h => hyx (congrArg Subtype.val h)
  · exact fun h => hyx2 (by simpa using congrArg Subtype.val h)

end Concrete

end Flag

end SBd8

end CFSG.Quasithin

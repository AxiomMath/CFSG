module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingClassClosure

import Mathlib.Tactic.Ring.RingNF

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.InvolutionCounting

variable {G : Type*} [Group G]

@[expose] def oddProductPairs (z w : G) : Set (G × G) :=
  {p | IsConj z p.1 ∧ p.1 ∈ Subgroup.centralizer {w} ∧ IsConj z p.2 ∧
    p.2 ∈ Subgroup.centralizer {w} ∧ Odd (orderOf (p.1 * p.2))}

@[simp]
theorem mem_oddProductPairs {z w : G} {p : G × G} :
    p ∈ oddProductPairs z w ↔ IsConj z p.1 ∧ p.1 ∈ Subgroup.centralizer {w} ∧ IsConj z p.2 ∧
      p.2 ∈ Subgroup.centralizer {w} ∧ Odd (orderOf (p.1 * p.2)) :=
  Iff.rfl

theorem mem_thompsonPairs_cases [Finite G] {z u w : G} (hz : orderOf z = 2)
    (hu : orderOf u = 2) (hzu : ¬ IsConj z u)
    (hcomm : ∀ r s : G, IsConj z r → IsConj z s → Even (orderOf (r * s)) → Commute r s)
    (hprod : ∀ r s : G, IsConj z r → IsConj z s → r ≠ s → Commute r s → IsConj z (r * s))
    (hmixed : ∀ v r : G, IsConj u v → IsConj z r → Commute v r → IsConj u (v * r))
    (hw : orderOf w = 2) {p : G × G} (hp : p ∈ thompsonPairs u z w) :
    (IsConj u w ∧ IsConj z (w * p.1) ∧ Odd (orderOf (w * p.1 * p.2))) ∨
      (IsConj z w ∧ (p.1 * p.2) ^ 2 = w) := by
  obtain ⟨h1, h2, hmem⟩ := hp
  have hz2 := mul_self_eq_one_of_orderOf_eq_two hz
  have hv := mul_self_eq_one_of_isConj (mul_self_eq_one_of_orderOf_eq_two hu) h1
  have hvs : ¬ IsConj p.1 p.2 := fun h =>
    hzu (isConj_comm.mp ((h1.trans h).trans (isConj_comm.mp h2)))
  obtain ⟨d, hd0, hd⟩ := exists_orderOf_mul_eq_two_mul hv (mul_self_eq_one_of_isConj hz2 h2) hvs
  have hwc : w = (p.1 * p.2) ^ d := (mem_zpowers_iff_eq_pow_half hd hd0 hw).mp hmem
  rcases Nat.even_or_odd d with heven | hodd
  · obtain ⟨rfl, hsq⟩ := eq_two_and_isConj_sq_of_even hz2 hv h2 hcomm hprod hd hd0 heven
    exact Or.inr ⟨hwc ▸ hsq, hwc.symm⟩
  · obtain ⟨hr, hrv⟩ := isConj_pow_mul_and_commute_of_odd hz2 hv h2 hd hodd
    rw [← hwc] at hr hrv
    have hvwv : p.1 * (w * p.1) = w := by rw [← hrv.eq, mul_assoc, hv, mul_one]
    refine Or.inl ⟨hvwv ▸ hmixed p.1 _ h1 hr hrv.symm, hr, ?_⟩
    obtain ⟨j, rfl⟩ := hodd
    refine Odd.of_dvd_nat ⟨j, rfl⟩ (orderOf_dvd_of_pow_eq_one ?_)
    rw [hwc, mul_assoc, ← pow_succ, ← pow_mul,
      show (2 * j + 1 + 1) * (2 * j + 1) = 2 * (2 * j + 1) * (j + 1) by ring, pow_mul, ← hd,
      pow_orderOf_eq_one, one_pow]

theorem involution_pair_dihedral_support_and_odd_product_bijection [Finite G] {z u : G}
    (hz : orderOf z = 2) (hu : orderOf u = 2) (hzu : ¬ IsConj z u)
    (hcomm : ∀ r s : G, IsConj z r → IsConj z s → Even (orderOf (r * s)) → Commute r s)
    (hprod : ∀ r s : G, IsConj z r → IsConj z s → r ≠ s → Commute r s → IsConj z (r * s))
    (hmixed : ∀ v r : G, IsConj u v → IsConj z r → Commute v r → IsConj u (v * r)) :
    (∀ w : G, orderOf w = 2 → ¬ IsConj u w → ¬ IsConj z w → thompsonPairCount u z w = 0) ∧
    (∀ w : G, IsConj u w →
      Set.BijOn (fun p : G × G => (w * p.1, p.2)) (thompsonPairs u z w)
          (oddProductPairs z w) ∧
        Set.InvOn (fun p : G × G => (w * p.1, p.2)) (fun p : G × G => (w * p.1, p.2))
          (thompsonPairs u z w) (oddProductPairs z w)) ∧
    (∀ w : G, IsConj z w → thompsonPairs u z w =
      {p : G × G | IsConj u p.1 ∧ p.1 ∈ Subgroup.centralizer {w} ∧ IsConj z p.2 ∧
        p.2 ∈ Subgroup.centralizer {w} ∧ (p.1 * p.2) ^ 2 = w}) ∧
    Nat.card G = Nat.card (Subgroup.centralizer {z}) * thompsonPairCount u z u +
      Nat.card (Subgroup.centralizer {u}) * thompsonPairCount u z z := by
  have hz2 := mul_self_eq_one_of_orderOf_eq_two hz
  have hu2 := mul_self_eq_one_of_orderOf_eq_two hu
  have hcases := fun {w : G} (hw : orderOf w = 2) {p : G × G} (hp : p ∈ thompsonPairs u z w) =>
    mem_thompsonPairs_cases hz hu hzu hcomm hprod hmixed hw hp
  have hvanish : ∀ w : G, orderOf w = 2 → ¬ IsConj u w → ¬ IsConj z w →
      thompsonPairCount u z w = 0 := by
    intro w hw hwu hwz
    refine Nat.card_eq_zero.mpr (Or.inl ⟨fun p => ?_⟩)
    rcases hcases hw p.2 with h | h
    · exact hwu h.1
    · exact hwz h.1
  refine ⟨hvanish, fun w hwU => ?_, fun w hwD => ?_,
    card_eq_of_thompsonPairCount_support hu hz (fun h => hzu (isConj_comm.mp h)) hvanish⟩
  · have hw : orderOf w = 2 := (orderOf_eq_of_isConj hwU).symm.trans hu
    have hw2 := mul_self_eq_one_of_orderOf_eq_two hw
    have hinvol : ∀ p : G × G, (w * (w * p.1), p.2) = p := fun p => by
      rw [← mul_assoc, hw2, one_mul]
    have hwC : w ∈ Subgroup.centralizer {w} := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hinv : Set.InvOn (fun p : G × G => (w * p.1, p.2)) (fun p : G × G => (w * p.1, p.2))
        (thompsonPairs u z w) (oddProductPairs z w) :=
      ⟨fun p _ => hinvol p, fun p _ => hinvol p⟩
    refine ⟨hinv.bijOn (fun p hp => ?_) (fun p hp => ?_), hinv⟩
    · obtain ⟨h1C, h2C⟩ := mem_centralizer_of_mem_thompsonPairs hu2 hz2 hw2 hp
      rcases hcases hw hp with ⟨-, hr, hodd⟩ | ⟨hwD, -⟩
      · exact ⟨hr, Subgroup.mul_mem _ hwC h1C, hp.2.1, h2C, hodd⟩
      · exact absurd (hwU.trans (isConj_comm.mp hwD)) fun h => hzu (isConj_comm.mp h)
    · obtain ⟨hr, hrC, hs, hsC, hodd⟩ := hp
      have hwr : Commute w p.1 := (Subgroup.mem_centralizer_singleton_iff.mp hrC).symm
      have hws : Commute w p.2 := (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
      refine ⟨hmixed w p.1 hwU hr hwr, hs, ?_⟩
      obtain ⟨k, hk⟩ := hodd
      refine Subgroup.mem_zpowers_iff.mpr ⟨(orderOf (p.1 * p.2) : ℤ), ?_⟩
      rw [zpow_natCast, mul_assoc, (hwr.mul_right hws).mul_pow, pow_orderOf_eq_one, mul_one, hk,
        pow_succ, pow_mul, sq, hw2, one_pow, one_mul]
  · have hw : orderOf w = 2 := (orderOf_eq_of_isConj hwD).symm.trans hz
    have hw2 := mul_self_eq_one_of_orderOf_eq_two hw
    ext p
    refine ⟨fun hp => ?_, fun ⟨h1, _, h2, _, hsq⟩ => ⟨h1, h2, hsq ▸ Subgroup.npow_mem_zpowers _ 2⟩⟩
    obtain ⟨h1C, h2C⟩ := mem_centralizer_of_mem_thompsonPairs hu2 hz2 hw2 hp
    rcases hcases hw hp with ⟨hwU, -⟩ | ⟨-, hsq⟩
    · exact absurd (isConj_comm.mp (hwU.trans (isConj_comm.mp hwD))) hzu
    · exact ⟨hp.1, h1C, hp.2.1, h2C, hsq⟩

theorem thompsonPairCount_eq_card_oddProductPairs [Finite G] {z u w : G} (hz : orderOf z = 2)
    (hu : orderOf u = 2) (hzu : ¬ IsConj z u)
    (hcomm : ∀ r s : G, IsConj z r → IsConj z s → Even (orderOf (r * s)) → Commute r s)
    (hprod : ∀ r s : G, IsConj z r → IsConj z s → r ≠ s → Commute r s → IsConj z (r * s))
    (hmixed : ∀ v r : G, IsConj u v → IsConj z r → Commute v r → IsConj u (v * r))
    (hwU : IsConj u w) :
    thompsonPairCount u z w = Nat.card (oddProductPairs z w) :=
  Nat.card_congr (Set.BijOn.equiv _ ((involution_pair_dihedral_support_and_odd_product_bijection
    hz hu hzu hcomm hprod hmixed).2.1 w hwU).1)

end CFSG.ShultStronglyClosedTI.InvolutionCounting

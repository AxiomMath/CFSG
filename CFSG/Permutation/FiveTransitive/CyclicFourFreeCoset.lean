module

public import CFSG.Permutation.FiveTransitive.CyclicFourSumParity
public import CFSG.Permutation.FiveTransitive.CentralFreeFixedBound
public import CFSG.Permutation.FiveTransitive.NormalizerCosetCount
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitHom
public import CFSG.Permutation.FiveTransitive.CosetFixedSquare

public section

namespace CFSG

namespace FiveTransitive.CyclicFourFreeCoset

open MulAction
open scoped BigOperators

theorem counts
    {G Y : Type*} [Group G] [Finite Y] [MulAction G Y]
    (Q : Subgroup G) [Finite Q] (hQ : Nat.card Q = 4)
    (hfree : ∀ (q : Q) (z : Y), q • z = z → q = 1)
    (b : Q) (hb : orderOf b = 4)
    (y : Subgroup.normalizer (Q : Set G)) (hy2 : y.val ^ 2 = 1)
    (hcomm : ∀ q : Q, Commute q.val y.val)
    (heven : Even (Nat.card (orbitRel.Quotient Q Y)))
    (hypos : ∃ z : Y, y.val • z = z)
    (hybound : Nat.card (fixedBy Y y.val) ≤ 4)
    (haybound : Nat.card (fixedBy Y (b.val ^ 2 * y.val)) ≤ 4) :
    Nat.card (fixedBy Y y.val) = 4 ∧
      Nat.card (fixedBy Y (b.val ^ 2 * y.val)) = 4 ∧
      Nat.card (fixedBy Y (b.val * y.val)) = 0 ∧
      Nat.card (fixedBy Y (b.val ^ 3 * y.val)) = 0 ∧
      Disjoint (fixedBy Y y.val) (fixedBy Y (b.val ^ 2 * y.val)) ∧
      Nat.card (Function.fixedPoints (NormalizerOrbitPermutation.orbitPerm (Y := Y) Q y)) = 2 := by
  classical
  let _ : Fintype Q := Fintype.ofFinite _
  have hbG : orderOf b.val = 4 := (Subgroup.orderOf_coe b).trans hb
  have hb4 : b.val ^ 4 = 1 := hbG ▸ pow_orderOf_eq_one b.val
  have hb2ne : b.val ^ 2 ≠ 1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [hbG] at hd
    norm_num at hd
  have hzero (g : G) (hg : g ^ 2 = b.val ^ 2) : Nat.card (fixedBy Y g) = 0 := by
    have he : fixedBy Y g = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hsq := CosetFixedSquare.eq_one_of_square_mem Q hfree g
        (by rw [hg]; exact Q.pow_mem b.property 2) z hz
      exact hb2ne (hg.symm.trans hsq)
    rw [Nat.card_coe_set_eq, he, Set.ncard_empty]
  have hbzero : Nat.card (fixedBy Y (b.val * y.val)) = 0 := hzero _ (by
    rw [(hcomm b).mul_pow, hy2, mul_one])
  have hb3zero : Nat.card (fixedBy Y (b.val ^ 3 * y.val)) = 0 := hzero _ (by
    rw [((hcomm b).pow_left 3).mul_pow, hy2, mul_one, ← pow_mul]
    calc
      b.val ^ (3 * 2) = b.val ^ 4 * b.val ^ 2 := by rw [← pow_add]
      _ = b.val ^ 2 := by rw [hb4, one_mul])
  obtain ⟨z, hz⟩ := hypos
  have hlower := CentralFreeFixedBound.card_le_fixed Q z (fun q => hfree q z) y.val hz hcomm
  rw [← Nat.card_coe_set_eq, hQ] at hlower
  have hyfour : Nat.card (fixedBy Y y.val) = 4 := by omega
  have hysq : y ^ 2 = 1 := Subtype.ext hy2
  have hp2 : (NormalizerOrbitPermutation.orbitPerm (Y := Y) Q y) ^ 2 = 1 := by
    change (NormalizerOrbitHom.toPermHom (Y := Y) Q y) ^ 2 = 1
    rw [← map_pow, hysq, map_one]
  have hpar := CyclicFourSumParity.even_fixed
    (NormalizerOrbitPermutation.orbitPerm (Y := Y) Q y) hp2 heven
  have hsum := NormalizerCosetCount.fixed_sum Q hfree y
  rw [CyclicFourSumParity.sum_four hQ b hb, hQ] at hsum
  simp only [OneMemClass.coe_one, one_mul, Subgroup.coe_pow] at hsum
  rw [hyfour, hbzero, hb3zero] at hsum
  obtain ⟨n, hn⟩ := hpar
  have horbits : Nat.card (Function.fixedPoints
      (NormalizerOrbitPermutation.orbitPerm (Y := Y) Q y)) = 2 := by omega
  have hayfour : Nat.card (fixedBy Y (b.val ^ 2 * y.val)) = 4 := by omega
  refine ⟨hyfour, hayfour, hbzero, hb3zero, ?_, horbits⟩
  rw [Set.disjoint_left]
  intro t ht hut
  have ha : (⟨b.val ^ 2, Q.pow_mem b.property 2⟩ : Q) • t = t := by
    change (b.val ^ 2) • t = t
    change (b.val ^ 2 * y.val) • t = t at hut
    rwa [mul_smul, show y.val • t = t from ht] at hut
  exact hb2ne (congrArg Subtype.val (hfree _ t ha))

end FiveTransitive.CyclicFourFreeCoset

end CFSG

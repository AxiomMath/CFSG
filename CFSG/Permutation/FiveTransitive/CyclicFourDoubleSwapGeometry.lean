module

public import CFSG.Permutation.FiveTransitive.CyclicFourDoubleSwap
public import CFSG.Permutation.FiveTransitive.NormalizerUniqueOrbitGeometry

public section

namespace CFSG

namespace FiveTransitive.CyclicFourDoubleSwapGeometry

open MulAction NormalizerFixedComplement

theorem fixed_eq_orbit
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : Nat.card Q = 4)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (u : Normalizer Q) (hcomm : ∀ q : Q, Commute q.val u.val)
    (hfixed : (fixedBy X u.val \ fixedPoints Q X).ncard = 4)
    (z : Domain (X := X) Q) (hz : u.val • z.val = z.val) :
    fixedBy X u.val \ fixedPoints Q X = orbit Q z.val := by
  have hsub : orbit Q z.val ⊆ fixedBy X u.val \ fixedPoints Q X := by
    intro t ht
    refine ⟨?_, NormalizerUniqueOrbitGeometry.orbit_outside Q z ht⟩
    obtain ⟨q, rfl⟩ := mem_orbit_iff.mp ht
    change u.val • (q.val • z.val) = q.val • z.val
    rw [← mul_smul, ← (hcomm q).eq, mul_smul, hz]
  have hc : (orbit Q z.val).ncard = 4 := (NormalizerUniqueOrbitGeometry.orbit_card Q hfree z).trans hQ
  exact (Set.eq_of_subset_of_ncard_le hsub (by omega)).symm

theorem exists_two_orbits
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q : Subgroup G) (hQ : Nat.card Q = 4)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (hdiv : 8 ∣ Nat.card X - 7)
    (b : Q) (hb : orderOf b = 4)
    (y : Normalizer Q) (hy : orderOf y.val = 2)
    (hcomm : ∀ q : Q, Commute q.val y.val)
    (hlocal : (fixedBy X y.val ∩ fixedPoints Q X).ncard = 3)
    (hypos : ∃ t : X, t ∉ fixedPoints Q X ∧ y.val • t = t) :
    (fixedBy X y.val \ fixedPoints Q X).ncard = 4 ∧
      (fixedBy X (b.val ^ 2 * y.val) \ fixedPoints Q X).ncard = 4 ∧
      (fixedBy X (b.val * y.val) \ fixedPoints Q X).ncard = 0 ∧
      (fixedBy X (b.val⁻¹ * y.val) \ fixedPoints Q X).ncard = 0 ∧
      Nat.card (Function.fixedPoints (NormalizerSevenOrbitCount.orbitPerm (X := X) Q y)) = 2 ∧
      ∃ z w : Domain (X := X) Q,
        y.val • z.val = z.val ∧ (b.val ^ 2 * y.val) • w.val = w.val ∧
        fixedBy X y.val \ fixedPoints Q X = orbit Q z.val ∧
        fixedBy X (b.val ^ 2 * y.val) \ fixedPoints Q X = orbit Q w.val ∧
        (orbit Q z.val).ncard = 4 ∧ (orbit Q w.val).ncard = 4 ∧
        Disjoint (orbit Q z.val) (orbit Q w.val) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hyfour, hafour, hbzero, hbizero, hdis, htwo⟩ := CyclicFourDoubleSwap.counts
    hmax Q hQ hseven hfree (CyclicFourDoubleSwap.even_orbit_card Q hQ hseven hfree hdiv)
    b hb y hy hcomm hlocal hypos
  obtain ⟨z, hzy, hzF⟩ := (Set.ncard_pos (Set.toFinite _)).mp (show 0 <
    (fixedBy X y.val \ fixedPoints Q X).ncard by omega)
  obtain ⟨w, hwa, hwF⟩ := (Set.ncard_pos (Set.toFinite _)).mp (show 0 <
    (fixedBy X (b.val ^ 2 * y.val) \ fixedPoints Q X).ncard by omega)
  let zD : Domain (X := X) Q := ⟨z, hzF⟩
  let wD : Domain (X := X) Q := ⟨w, hwF⟩
  let ay : Normalizer Q := ⟨b.val ^ 2 * y.val,
    (Normalizer Q).mul_mem ((Normalizer Q).pow_mem (Q.le_normalizer b.property) 2) y.property⟩
  have hQcomm : ∀ q r : Q, q * r = r * q := isMulCommutative_iff.mp
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hQ))
  have hacomm (q : Q) : Commute q.val ay.val := by
    have hqb : Commute q.val b.val := congrArg (fun q : Q => q.val) (hQcomm q b)
    exact (hqb.pow_right 2).mul_right (hcomm q)
  have hyorb := fixed_eq_orbit Q hQ hfree y hcomm hyfour zD hzy
  have haorb := fixed_eq_orbit Q hQ hfree ay hacomm hafour wD hwa
  refine ⟨hyfour, hafour, hbzero, hbizero, htwo, zD, wD, hzy, hwa, hyorb, haorb, ?_, ?_, ?_⟩
  · rwa [← hyorb]
  · rwa [← haorb]
  · rwa [← hyorb, ← haorb]

end FiveTransitive.CyclicFourDoubleSwapGeometry

end CFSG

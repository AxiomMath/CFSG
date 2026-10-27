module

public import Mathlib.GroupTheory.SpecificGroups.KleinFour

namespace CFSG
end CFSG
open CFSG

/-!
# Automorphisms of a Klein four-group fixing a nonidentity element

This module isolates the elementary automorphism calculation used in the
Klein-four normalizer analysis for Gorenstein--Walter Part I, Lemma 2.2.
-/

namespace CFSG.GorensteinWalter

/-- An automorphism of a Klein four-group that fixes a nonidentity element
has square one. -/
public theorem mulAut_sq_eq_one_of_fixed_ne_one
    {V : Type*} [Group V] [IsKleinFour V]
    (φ : MulAut V) {t : V} (ht : t ≠ 1) (hfix : φ t = t) :
    φ ^ 2 = 1 := by
  ext z
  change φ (φ z) = z
  by_cases hz1 : z = 1
  · subst z
    simp
  by_cases hzt : z = t
  · subst z
    simp [hfix]
  by_cases hφz : φ z = z
  · rw [hφz]
    exact hφz
  have hφz1 : φ z ≠ 1 := by
    simpa using hz1
  have hφzt : φ z ≠ t := by
    intro h
    apply hzt
    apply φ.injective
    rw [h, hfix]
  have himage : φ z = t * z :=
    IsKleinFour.eq_mul_of_ne_all ht hz1 (fun h => hzt h.symm) hφz1 hφzt hφz
  calc
    φ (φ z) = φ (t * z) := by rw [himage]
    _ = φ t * φ z := φ.map_mul t z
    _ = t * (t * z) := by rw [hfix, himage]
    _ = z := by rw [← mul_assoc, IsKleinFour.mul_self, one_mul]

end CFSG.GorensteinWalter

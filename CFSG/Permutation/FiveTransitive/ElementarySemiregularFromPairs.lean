module

public import CFSG.Permutation.FiveTransitive.ElementaryEightFixedExclusion
public import CFSG.Permutation.FiveTransitive.ElementaryFourOrbitExclusion

public section

namespace CFSG

namespace FiveTransitive.ElementarySemiregularFromPairs

open MulAction

theorem semiregular
    {G X : Type*} [CommGroup G] [Finite X] [MulAction G X]
    (h2 : ∀ g : G, g * g = 1)
    (hmax : ∀ g : G, g ≠ 1 → (fixedBy X g).ncard ≤ 7)
    (T : Set X) (hT : ∀ (g : G) (t : X), t ∈ T → g • t ∈ T)
    (a b c d : G)
    (hmove : ∀ g ∈ ({a, b, c, d, a * b, a * c, a * d, b * c, b * d, c * d} : Set G),
      ∀ t ∉ T, g • t ≠ t)
    (habc : a * b * c ≠ 1)
    (hinside : 3 ≤ (fixedBy X (a * b * c) ∩ T).ncard) :
    ∀ g : G, g ≠ 1 → ∀ t ∉ T, g • t ≠ t := by
  have hbound : (fixedBy X (a * b * c) \ T).ncard ≤ 4 := by
    have hsum := Set.ncard_inter_add_ncard_sdiff_eq_ncard (fixedBy X (a * b * c)) T
    have hm := hmax (a * b * c) habc
    omega
  have htriple := ElementaryFourOrbitExclusion.no_threefold_fixed h2 T hT a b c d hbound
    (hmove a (by simp)) (hmove b (by simp)) (hmove (a * b) (by simp))
    (hmove d (by simp)) (hmove (a * d) (by simp))
    (hmove (b * d) (by simp)) (hmove (c * d) (by simp))
  intro g hg t ht
  apply ElementaryEightFixedExclusion.no_fixed_of_seven_bound h2 a b c t _ g (hmax g hg)
  intro u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hmove u (by simp) t ht
  · exact hmove u (by simp) t ht
  · exact hmove u (by simp) t ht
  · exact hmove (a * b) (by simp) t ht
  · exact hmove (a * c) (by simp) t ht
  · exact hmove (b * c) (by simp) t ht
  · exact htriple t ht

end FiveTransitive.ElementarySemiregularFromPairs

end CFSG

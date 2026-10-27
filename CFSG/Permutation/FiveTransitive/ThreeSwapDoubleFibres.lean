module

public import CFSG.Permutation.FiveTransitive.CentralKernelSquareTransport
public import CFSG.Permutation.FiveTransitive.ThreeSwapNormalizerConjugators

public section

namespace CFSG

namespace FiveTransitive.ThreeSwapDoubleFibres

theorem square_eq_one
    {G F : Type*} [Group G] [DecidableEq F]
    (f : G →* Equiv.Perm F) (B K : Subgroup G)
    (hk : B ⊓ f.ker = K)
    (hcentral : ∀ q : K, ∀ g : G, (q : G) * g = g * q)
    (hKsq : ∀ q : K, (q : G) ^ 2 = 1)
    (e : Fin 6 ↪ F)
    (hn : (Subgroup.normalizer (B : Set G)).map f =
      Subgroup.normalizer (ThreeSwapTwoGroup.subgroup e : Set (Equiv.Perm F)))
    (y : G) (hyB : y ∈ B) (hy : y ^ 2 = 1)
    (hyf : f y = Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3))
    (u : B)
    (hu : f u.val = Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) ∨
      f u.val = Equiv.swap (e 0) (e 1) * Equiv.swap (e 4) (e 5) ∨
      f u.val = Equiv.swap (e 2) (e 3) * Equiv.swap (e 4) (e 5)) :
    u ^ 2 = 1 := by
  have hfy : (f y) ^ 2 = 1 := by rw [← map_pow, hy, map_one]
  have transport (c : G) (hc : c ∈ Subgroup.normalizer (B : Set G))
      (he : f (c * y * c⁻¹) = f u.val) : u ^ 2 = 1 := by
    apply Subtype.ext
    exact (CentralKernelSquareTransport.square_eq_of_image_conjugacy
      f B K hk hcentral hKsq y u.val c hyB u.property hc hfy he).symm.trans hy
  obtain ⟨_, b, c, _, _, hc, hb⟩ := ThreeSwapNormalizerConjugators.exists_conjugators e
  rcases hu with hu | hu | hu
  · apply transport 1 (Subgroup.one_mem _)
    simpa only [one_mul, inv_one, mul_one] using hyf.trans hu.symm
  · obtain ⟨g, hg, hfg⟩ := hn.ge c.property
    apply transport g hg
    simpa only [map_mul, map_inv, hfg, hyf, hu] using hc
  · obtain ⟨g, hg, hfg⟩ := hn.ge b.property
    apply transport g hg
    simpa only [map_mul, map_inv, hfg, hyf, hu] using hb

end FiveTransitive.ThreeSwapDoubleFibres

end CFSG

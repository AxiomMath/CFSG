module

public import CFSG.Permutation.FiveTransitive.ThreeInvolutionCompatibility
public import CFSG.Permutation.FiveTransitive.CentralKernelSquareTransport

public section

namespace CFSG

namespace FiveTransitive.ThreeSwapLiftCommutativity

private theorem commute_of_square
    {G : Type*} [Group G] (x y : G) (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x * y) * (x * y) = 1) : Commute x y := by
  have h : x * y * x = y := by
    have h := congrArg (fun t : G => t * y) hxy
    simpa only [mul_assoc, hy, mul_one, one_mul] using h
  have h' := congrArg (fun t : G => t * x) h
  exact (by simpa only [mul_assoc, hx, mul_one] using h' : x * y = y * x)

theorem pairwise_commute
    {G H X : Type*} [Group G] [Group H] [MulAction G X]
    (f : G →* H) (S Q : Subgroup G) (hker : S ⊓ f.ker = Q)
    (a : G) (ha : a * a = 1) (haQ : a ∈ Q)
    (hQmem : ∀ q ∈ Q, q = 1 ∨ q = a)
    (hcentral : ∀ q : Q, ∀ g : G, (q : G) * g = g * q)
    (x y z : G) (hxS : x ∈ S) (hyS : y ∈ S) (hzS : z ∈ S)
    (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1)
    (hxyf : (f (x * y)) ^ 2 = 1)
    (hxzf : (f (x * z)) ^ 2 = 1) (hyzf : (f (y * z)) ^ 2 = 1)
    (c13 c23 : G)
    (hc13 : c13 ∈ Subgroup.normalizer (S : Set G))
    (hc23 : c23 ∈ Subgroup.normalizer (S : Set G))
    (he13 : f (c13 * (x * z) * c13⁻¹) = f (x * y))
    (he23 : f (c23 * (y * z) * c23⁻¹) = f (x * y))
    (htwo : (MulAction.fixedBy X x \ MulAction.fixedBy X a).ncard = 2) :
    Commute x y ∧ Commute x z ∧ Commute y z := by
  have hQsq (q : Q) : (q : G) ^ 2 = 1 := by
    rcases hQmem q.val q.property with h | h
    · rw [h, one_pow]
    · rw [h, pow_two, ha]
  have hcases : (x * y) * (x * y) = 1 ∨ (x * y) * (x * y) = a := by
    apply hQmem
    apply hker.le
    refine ⟨S.mul_mem (S.mul_mem hxS hyS) (S.mul_mem hxS hyS), ?_⟩
    change f ((x * y) * (x * y)) = 1
    simpa only [pow_two, map_mul] using hxyf
  have h13 := CentralKernelSquareTransport.square_eq_of_image_conjugacy
    f S Q hker hcentral hQsq (x * z) (x * y) c13
    (S.mul_mem hxS hzS) (S.mul_mem hxS hyS) hc13 hxzf he13
  have h23 := CentralKernelSquareTransport.square_eq_of_image_conjugacy
    f S Q hker hcentral hQsq (y * z) (x * y) c23
    (S.mul_mem hyS hzS) (S.mul_mem hxS hyS) hc23 hyzf he23
  simp only [pow_two] at h13 h23
  have hxy := ThreeInvolutionCompatibility.pair_square_eq_one a x y z ha hx hy hz
    (hcentral ⟨a, haQ⟩ y) (hcentral ⟨a, haQ⟩ z) hcases h13 h23 htwo
  exact ⟨commute_of_square x y hx hy hxy,
    commute_of_square x z hx hz (h13.trans hxy),
    commute_of_square y z hy hz (h23.trans hxy)⟩

end FiveTransitive.ThreeSwapLiftCommutativity

end CFSG

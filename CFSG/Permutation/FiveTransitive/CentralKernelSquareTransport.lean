module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG

namespace FiveTransitive.CentralKernelSquareTransport

theorem square_eq_of_image_conjugacy
    {G H : Type*} [Group G] [Group H] (f : G →* H) (S Q : Subgroup G)
    (hker : S ⊓ f.ker = Q)
    (hcentral : ∀ q : Q, ∀ g : G, (q : G) * g = g * q)
    (hQsq : ∀ q : Q, (q : G) ^ 2 = 1)
    (x y c : G) (hx : x ∈ S) (hy : y ∈ S)
    (hc : c ∈ Subgroup.normalizer (S : Set G))
    (hfx : (f x) ^ 2 = 1)
    (himage : f (c * x * c⁻¹) = f y) : x ^ 2 = y ^ 2 := by
  let q : G := (c * x * c⁻¹) * y⁻¹
  have hqS : q ∈ S := S.mul_mem ((Subgroup.mem_normalizer_iff.mp hc x).mp hx) (S.inv_mem hy)
  have hqK : q ∈ f.ker := by
    change f ((c * x * c⁻¹) * y⁻¹) = 1
    rw [map_mul, himage, map_inv, mul_inv_cancel]
  have hqQ : q ∈ Q := hker.le ⟨hqS, hqK⟩
  have hxsqQ : x ^ 2 ∈ Q := hker.le ⟨S.pow_mem hx 2, by
    change f (x ^ 2) = 1
    rw [map_pow, hfx]⟩
  have hq2 : q ^ 2 = 1 := hQsq ⟨q, hqQ⟩
  have hqy : Commute q y := hcentral ⟨q, hqQ⟩ y
  have he : c * x * c⁻¹ = q * y := by dsimp [q]; group
  have he2 : (c * x * c⁻¹) ^ 2 = y ^ 2 := by
    rw [he, hqy.mul_pow, hq2, one_mul]
  have hcsq : c * x ^ 2 * c⁻¹ = x ^ 2 := by
    rw [← hcentral ⟨x ^ 2, hxsqQ⟩ c]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  rwa [conj_pow, hcsq] at he2

end FiveTransitive.CentralKernelSquareTransport

end CFSG

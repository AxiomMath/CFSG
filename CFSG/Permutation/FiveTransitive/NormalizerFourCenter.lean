module

public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG

namespace FiveTransitive.NormalizerFourCenter

private theorem conjugate_mem_centralizer
    {G : Type*} [Group G] (R : Subgroup G) (q n : G)
    (hq : q ∈ Subgroup.centralizer (R : Set G))
    (hn : n ∈ Subgroup.normalizer (R : Set G)) :
    n * q * n⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
  let f := (MulAut.conj n).toMonoidHom
  have hx : f q ∈ (Subgroup.centralizer (R : Set G)).map f :=
    Subgroup.mem_map_of_mem f hq
  have h := Subgroup.map_centralizer_le_centralizer_image (R : Set G) f hx
  have hm : R.map f = R := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hs : f '' (R : Set G) = (R : Set G) := by
    change (R.map f : Set G) = (R : Set G)
    rw [hm]
  rw [hs] at h
  exact h

theorem conjugate_eq_or_twist
    {G : Type*} [Group G] (R : Subgroup G) (q z : G)
    (hqR : q ∈ R) (hqC : q ∈ Subgroup.centralizer (R : Set G))
    (hq1 : q ≠ 1) (hqz : q ≠ z)
    (hzN : ∀ n ∈ Subgroup.normalizer (R : Set G), n * z = z * n)
    (hcenter : ∀ x ∈ R, (∀ y ∈ R, x * y = y * x) →
      x = 1 ∨ x = q ∨ x = z ∨ x = q * z) :
    ∀ n ∈ Subgroup.normalizer (R : Set G), n * q * n⁻¹ = q ∨ n * q * n⁻¹ = q * z := by
  intro n hn
  have hxR : n * q * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hn q).mp hqR
  have hxC := conjugate_mem_centralizer R q n hqC hn
  have hxcent : ∀ y ∈ R, (n * q * n⁻¹) * y = y * (n * q * n⁻¹) := by
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp hxC) y hy).symm
  have hz : n * z * n⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr (hzN n hn)
  rcases hcenter _ hxR hxcent with h | h | h | h
  · have he : (MulAut.conj n) q = (MulAut.conj n) 1 := by simpa only [map_one, MulAut.conj_apply] using h
    exact (hq1 ((MulAut.conj n).injective he)).elim
  · exact Or.inl h
  · exact (hqz ((MulAut.conj n).injective (h.trans hz.symm))).elim
  · exact Or.inr h

end FiveTransitive.NormalizerFourCenter

end CFSG

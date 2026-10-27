module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# An involution normalizes a subgroup--conjugate intersection

Conjugation by an element of square one swaps a subgroup with its conjugate.
Consequently it normalizes their intersection.  This is the intersection
control used for `Ĥ ⊓ Ĥ^y` in Gorenstein--Walter Theorem 2.6.
-/

namespace CFSG.GorensteinWalter

/-- If `y²=1`, then `y` normalizes `H ⊓ H^y`. -/
public theorem involution_mem_normalizer_inf_conjugateSubgroup
    {G : Type*} [Group G] (H : Subgroup G) {y : G}
    (hy2 : y * y = 1) :
    y ∈ Subgroup.normalizer
      ((H ⊓ conjugateSubgroup H y : Subgroup G) : Set G) := by
  have hyinv : y⁻¹ = y := (eq_inv_of_mul_eq_one_right hy2).symm
  have hflip (x : G) : y * (y * x * y⁻¹) * y⁻¹ = x := by
    rw [hyinv]
    calc
      y * (y * x * y) * y = (y * y) * x * (y * y) := by group
      _ = x := by rw [hy2]; simp
  have htoConj {x : G} (hx : x ∈ H) :
      y * x * y⁻¹ ∈ conjugateSubgroup H y := by
    change y * x * y⁻¹ ∈ H.map (MulAut.conj y).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hfromConj {x : G} (hx : x ∈ conjugateSubgroup H y) :
      y * x * y⁻¹ ∈ H := by
    change x ∈ H.map (MulAut.conj y).toMonoidHom at hx
    rcases Subgroup.mem_map.mp hx with ⟨h, hh, hval⟩
    change y * h * y⁻¹ = x at hval
    have heq : y * x * y⁻¹ = h := by
      calc
        y * x * y⁻¹ = y * (y * h * y⁻¹) * y⁻¹ := by rw [hval]
        _ = h := hflip h
    rw [heq]
    exact hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxH, hxHy⟩
    exact ⟨hfromConj hxHy, htoConj hxH⟩
  · rintro ⟨hconjH, hconjHy⟩
    have hbackH : y * (y * x * y⁻¹) * y⁻¹ ∈ H :=
      hfromConj hconjHy
    have hbackHy : y * (y * x * y⁻¹) * y⁻¹ ∈
        conjugateSubgroup H y :=
      htoConj hconjH
    rw [hflip x] at hbackH hbackHy
    exact ⟨hbackH, hbackHy⟩

end CFSG.GorensteinWalter

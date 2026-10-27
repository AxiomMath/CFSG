module

public import Mathlib.GroupTheory.PGroup

public noncomputable section

namespace CFSG.GroupTheory

open Subgroup

variable {E C : Type*} [Group E] [Group C] {π : E →* C}

@[expose] def centralTwoKernel (hc : π.ker ≤ center E) : Subgroup E where
  carrier := {z | z ∈ π.ker ∧ z ^ 2 = 1}
  one_mem' := ⟨π.ker.one_mem, one_pow 2⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨π.ker.mul_mem hx.1 hy.1, ?_⟩
    have hxy : Commute x y := (mem_center_iff.mp (hc hx.1) y).symm
    rw [hxy.mul_pow, hx.2, hy.2, one_mul]
  inv_mem' := by
    intro x hx
    refine ⟨π.ker.inv_mem hx.1, ?_⟩
    rw [inv_pow, hx.2, inv_one]

@[simp] theorem mem_centralTwoKernel (hc : π.ker ≤ center E) (z : E) :
    z ∈ centralTwoKernel hc ↔ z ∈ π.ker ∧ z ^ 2 = 1 := Iff.rfl

theorem centralTwoKernel_le_ker (hc : π.ker ≤ center E) :
    centralTwoKernel hc ≤ π.ker := fun _ hz => hz.1

theorem centralTwoKernel_le_center (hc : π.ker ≤ center E) :
    centralTwoKernel hc ≤ center E := (centralTwoKernel_le_ker hc).trans hc

instance centralTwoKernel_normal (hc : π.ker ≤ center E) :
    (centralTwoKernel hc).Normal := normal_of_le_center (centralTwoKernel_le_center hc)

theorem centralTwoKernel_isPGroup (hc : π.ker ≤ center E) :
    IsPGroup 2 (centralTwoKernel hc) := by
  intro z
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa using z.property.2

theorem eq_one_of_cube_eq_one_of_two_quotient_eq_one (hc : π.ker ≤ center E)
    {z : E} (h3 : z ^ 3 = 1)
    (hq : QuotientGroup.mk' (centralTwoKernel hc) z = 1) : z = 1 := by
  have h2 := ((QuotientGroup.eq_one_iff z).mp hq).2
  calc
    z = z ^ 3 * (z ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp

@[expose] def centralTwoQuotientMap (hc : π.ker ≤ center E) :
    E ⧸ centralTwoKernel hc →* C :=
  QuotientGroup.lift (centralTwoKernel hc) π (centralTwoKernel_le_ker hc)

@[simp] theorem centralTwoQuotientMap_mk (hc : π.ker ≤ center E) (z : E) :
    centralTwoQuotientMap hc (QuotientGroup.mk' (centralTwoKernel hc) z) = π z := rfl

theorem centralTwoQuotientMap_ker_le_center (hc : π.ker ≤ center E) :
    (centralTwoQuotientMap hc).ker ≤ center (E ⧸ centralTwoKernel hc) := by
  intro z hz
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (centralTwoKernel hc) z
  have hx : x ∈ π.ker := hz
  exact Subgroup.map_center_le_center
    (QuotientGroup.mk'_surjective (centralTwoKernel hc)) ⟨x, hc hx, rfl⟩
theorem centralTwoKernel_map_eq (hc : π.ker ≤ center E) (α : MulAut E)
    (δ : MulAut C) (hcompat : ∀ z, π (α z) = δ (π z)) :
    (centralTwoKernel hc).map α.toMonoidHom = centralTwoKernel hc := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · change π (α x) = 1
      rw [hcompat, MonoidHom.mem_ker.mp hx.1, map_one]
    · change (α x) ^ 2 = 1
      rw [← map_pow, hx.2, map_one]
  · intro hz
    refine ⟨α.symm z, ⟨?_, ?_⟩, α.apply_symm_apply z⟩
    · apply δ.injective
      rw [map_one, ← hcompat, α.apply_symm_apply]
      exact hz.1
    · rw [← map_pow, hz.2, map_one]


end CFSG.GroupTheory

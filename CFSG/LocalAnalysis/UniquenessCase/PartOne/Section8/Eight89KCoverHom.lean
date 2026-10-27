module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KCoverPG

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

open Subgroup

private theorem k91ch_rel {H : Type*} [Group H] (n i j k l : ℕ) (x y z : H) (hzn : z ^ n = 1)
    (hxz : Commute x z) (hyz : Commute y z) (hx : x ^ 2 = z ^ (3 * i))
    (hy : y ^ 4 = z ^ (3 * j)) (hk : (x * y) ^ 5 = z ^ k) (hl : (x * y * y) ^ 5 = z ^ l) :
    ∀ r ∈ {r : FreeGroup (Fin 3) | r ∈ (KData.coverWords n i j k l).map FreeGroup.mk},
      FreeGroup.lift ![x, y, z] r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  rw [FreeGroup.lift_mk]
  simp only [KData.coverWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [hzn]
  · simp [hxz.eq]
  · simp [hyz.eq]
  · simp
    rw [show x * (x * (z ^ (3 * i))⁻¹) = x ^ 2 * (z ^ (3 * i))⁻¹ by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc], hx, mul_inv_cancel]
  · simp
    rw [show y * (y * (y * (y * (z ^ (3 * j))⁻¹))) = y ^ 4 * (z ^ (3 * j))⁻¹ by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc], hy, mul_inv_cancel]
  · simp
    rw [show x * (y * (x * (y * (x * (y * (x * (y * (x * (y * (z ^ k)⁻¹))))))))) =
      (x * y) ^ 5 * (z ^ k)⁻¹ by simp only [pow_succ, pow_zero, one_mul, mul_assoc], hk,
      mul_inv_cancel]
  · simp
    rw [show x * (y * (y * (x * (y * (y * (x * (y * (y * (x * (y * (y * (x * (y * (y *
      (z ^ l)⁻¹)))))))))))))) = (x * y * y) ^ 5 * (z ^ l)⁻¹ by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc], hl, mul_inv_cancel]

theorem exists_coverHom {H : Type*} [Group H] (n i j k l : ℕ) (x y z : H) (hzn : z ^ n = 1)
    (hxz : Commute x z) (hyz : Commute y z) (hx : x ^ 2 = z ^ (3 * i))
    (hy : y ^ 4 = z ^ (3 * j)) (hk : (x * y) ^ 5 = z ^ k) (hl : (x * y * y) ^ 5 = z ^ l) :
    ∃ φ : CoverPG n i j k l →* H, φ (PresentedGroup.of (0 : Fin 3)) = x ∧
      φ (PresentedGroup.of (1 : Fin 3)) = y ∧ φ (PresentedGroup.of (2 : Fin 3)) = z ∧
      φ.range = closure {x, y, z} := by
  let φ : CoverPG n i j k l →* H :=
    PresentedGroup.toGroup (f := ![x, y, z]) (k91ch_rel n i j k l x y z hzn hxz hyz hx hy hk hl)
  have hof : ∀ a : Fin 3, φ (PresentedGroup.of a) = ![x, y, z] a := fun a =>
    PresentedGroup.toGroup.of _
  refine ⟨φ, hof 0, hof 1, hof 2, ?_⟩
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp, show ⇑φ ∘ PresentedGroup.of = ![x, y, z] from funext hof]
  congr 1
  ext g
  simp
  tauto

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

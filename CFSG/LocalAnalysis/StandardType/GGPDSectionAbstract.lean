module

public import Mathlib.Algebra.Group.Subgroup.Basic

public section

namespace CFSG.StandardType

theorem ggPD_exists_section_of_inversion_equivariant
    {E A : Type*} [CommGroup E] [Group A]
    (q : E →* A) (hq : Function.Surjective q)
    (f : MulAut E)
    (hfix : ∀ y ∈ q.ker, f y = y)
    (hinv : ∀ y, q (f y) = (q y)⁻¹)
    (hexp : ∀ a : A, a ^ 3 = 1) :
    ∃ s : A →* E, (∀ a, q (s a) = a) ∧
      (∀ y, s (q y) = f y * y⁻¹) ∧
      (∀ a, f (s a) = s a⁻¹) := by
  classical
  let r : E →* E :=
    { toFun := fun y => f y / y
      map_one' := by simp
      map_mul' := fun y z => by rw [map_mul, div_mul_div_comm] }
  have hker : q.ker ≤ r.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    change f y / y = 1
    rw [hfix y hy, div_self']
  let s : A →* E := MonoidHom.liftOfSurjective q hq ⟨r, hker⟩
  have hs : ∀ y, s (q y) = f y * y⁻¹ := by
    intro y
    change (MonoidHom.liftOfSurjective q hq ⟨r, hker⟩) (q y) = f y * y⁻¹
    rw [MonoidHom.liftOfRightInverse_comp_apply]
    change f y / y = f y * y⁻¹
    rw [div_eq_mul_inv]
  have hqs : ∀ a, q (s a) = a := by
    intro a
    obtain ⟨y, rfl⟩ := hq a
    rw [hs y, map_mul, map_inv, hinv y, ← mul_inv_rev]
    exact mul_eq_one_iff_inv_eq.mp (by simpa [pow_succ, sq] using hexp (q y))
  have hev : ∀ a, f (s a) = s a⁻¹ := by
    intro a
    obtain ⟨y, rfl⟩ := hq a
    rw [hs y, map_mul, map_inv, ← hinv y, hs (f y)]
  exact ⟨s, hqs, hs, hev⟩

end CFSG.StandardType

end

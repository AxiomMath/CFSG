module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.StandardType

theorem card_range_eq_of_central_quotient_equivariant
    {A J Q : Type*} [Group A] [Finite A] [Group J] [Group.IsPerfect J] [Group Q]
    (q : J →* Q) (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center J)
    (α : A →* MulAut J) (β : A →* MulAut Q)
    (heq : ∀ a j, q (α a j) = β a (q j)) : Nat.card α.range = Nat.card β.range := by
  have hK : α.ker = β.ker := by
    ext a
    change α a = 1 ↔ β a = 1
    constructor
    · intro hα
      ext x
      obtain ⟨j, rfl⟩ := hq x
      rw [← heq, hα, MulAut.one_apply, MulAut.one_apply]
    · intro hβ
      have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
        (α a).toMonoidHom (fun j => by
          apply hker
          rw [MonoidHom.mem_ker, map_mul, map_inv]
          change (q j)⁻¹ * q (α a j) = 1
          rw [heq, hβ, MulAut.one_apply, inv_mul_cancel])
      ext j
      exact congrArg (fun f : J →* J => f j) hid
  have hc := (Subgroup.card_ker_mul_card_range α).trans
    (Subgroup.card_ker_mul_card_range β).symm
  rw [hK] at hc
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos : 0 < Nat.card β.ker) hc

end CFSG.StandardType

end

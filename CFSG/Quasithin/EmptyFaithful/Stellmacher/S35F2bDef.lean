module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin1

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.F2b

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

@[expose] def fixQ {n : ℕ} (M : Model n) (B : Subgroup (Perm (Fin n))) (L : Subgroup M.W) :
    Subgroup M.W where
  carrier := {w | ∀ b ∈ B, M.act b w * w⁻¹ ∈ L}
  one_mem' := fun b _ => by simp
  mul_mem' := fun {x y} hx hy b hb => by
    have := L.mul_mem (hx b hb) (hy b hb)
    rw [map_mul]
    convert this using 1
    rw [mul_inv]; exact mul_mul_mul_comm _ _ _ _
  inv_mem' := fun {x} hx b hb => by
    have := L.inv_mem (hx b hb)
    rw [map_inv]
    convert this using 1
    rw [inv_inv]; simp [mul_inv_rev, mul_comm]

theorem mem_fixQ {n : ℕ} {M : Model n} {B : Subgroup (Perm (Fin n))} {L : Subgroup M.W}
    {w : M.W} : w ∈ fixQ M B L ↔ ∀ b ∈ B, M.act b w * w⁻¹ ∈ L := Iff.rfl

end CFSG.Quasithin.F53.Stellmacher.S35.F2b

module

public import CFSG.Open.LocalVocabulary
public import CFSG.RankThree.CentralExtension.InvariantComplement
public import CFSG.RankThree.Native.FiveLocalBasic

public section

namespace CFSG.RankThree.Native.FiveLocal

open Subgroup CFSG.Monster.B.Pinned CFSG.RankThree.CentralExtension
open scoped Matrix

variable {G : Type*} [Group G]

section Transport

variable {G' : Type*} [Group G'] (e : G ≃* G') {x h z : G} {q : Fin 4 → G}

theorem bcomm_map (a b : G) : bcomm (e a) (e b) = e (bcomm a b) := by
  simp only [bcomm, map_mul, map_inv]

theorem map_Q : (Q q).map e.toMonoidHom = Q (e ∘ q) := by
  rw [Q, Q, MonoidHom.map_closure, Set.range_comp]
  rfl

namespace Rel

variable (hR : Rel x h q z)
include hR

theorem map : Rel (e x) (e h) (e ∘ q) (e z) where
  commData :=
    { pow_q := fun i => by rw [Function.comp_apply, ← map_pow, hR.commData.pow_q i, map_one]
      orderOf_z := by rw [MulEquiv.orderOf_eq]; exact hR.orderOf_z
      comm_z := fun i => by rw [Function.comp_apply, ← map_mul, hR.commData.comm_z i, map_mul]
      bcomm_q := fun i j => by
        rw [Function.comp_apply, Function.comp_apply, bcomm_map, hR.commData.bcomm_q, map_pow]
      isUnit_det := hR.commData.isUnit_det
      mem_z := by
        have := mem_map_of_mem e.toMonoidHom hR.z_mem
        rw [map_Q] at this
        exact this }
  z_eq := by rw [Function.comp_apply, Function.comp_apply, bcomm_map, hR.z_eq]
  orderOf_x := by rw [MulEquiv.orderOf_eq]; exact hR.orderOf_x
  conj_x i := by
    rw [Function.comp_apply, ← map_inv, ← map_mul, ← map_mul, hR.conj_x i, map_mul, map_pow,
      map_list_prod, List.map_ofFn]
    simp only [Function.comp_def, map_pow]
  conj_xz := by rw [← map_inv, ← map_mul, ← map_mul, hR.conj_xz]
  conj_h i := by
    rw [Function.comp_apply, ← map_inv, ← map_mul, ← map_mul, hR.conj_h i, map_mul, map_pow,
      map_list_prod, List.map_ofFn]
    simp only [Function.comp_def, map_pow]
  conj_hz := by rw [← map_inv, ← map_mul, ← map_mul, hR.conj_hz, map_pow]

end Rel

end Transport

end CFSG.RankThree.Native.FiveLocal

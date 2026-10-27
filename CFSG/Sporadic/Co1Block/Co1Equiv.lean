
module

public import CFSG.Sporadic.Co1Block.PermBase
public import Certificates.Data.CFSGNative.Co1.Involutions

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier

theorem card_centralizer_co1
    (s : CFSG.Blueprint.NativeSporadic.Co1) :
    Nat.card (Subgroup.centralizer ({s} : Set CFSG.Blueprint.NativeSporadic.Co1)) =
      Nat.card (Subgroup.centralizer ({co1MatEquiv s} : Set GA)) := by
  refine Nat.card_congr
    { toFun := fun c => ⟨co1MatEquiv c, ?_⟩
      invFun := fun c => ⟨co1MatEquiv.symm c, ?_⟩
      left_inv := fun c => Subtype.ext (co1MatEquiv.symm_apply_apply _)
      right_inv := fun c => Subtype.ext (co1MatEquiv.apply_symm_apply _) }
  · have h := Subgroup.mem_centralizer_singleton_iff.1 c.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h]
  · have h := Subgroup.mem_centralizer_singleton_iff.1 c.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply co1MatEquiv.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h]

theorem orderOf_co1MatEquiv (s : CFSG.Blueprint.NativeSporadic.Co1) :
    orderOf (co1MatEquiv s) = orderOf s := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [← map_pow, ← (map_one co1MatEquiv), co1MatEquiv.injective.eq_iff]

theorem orderOf_co1MatEquiv_symm
    (g : GA) : orderOf (co1MatEquiv.symm g) = orderOf g := by
  rw [← orderOf_co1MatEquiv, MulEquiv.apply_symm_apply]

theorem validRows_one :
    CFSG.Sporadic.Co1.InvNative.validRows CFSG.Sporadic.Co1Schreier.Native.one = true := by
  show CFSG.Sporadic.Co1.InvNative.validRows (CFSG.Sporadic.SmallF2.Native.idRows 24) = true
  simp only [CFSG.Sporadic.Co1.InvNative.validRows, Bool.and_eq_true, beq_iff_eq,
    Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by simp [CFSG.Sporadic.SmallF2.Native.idRows], fun i hi => ?_⟩
  simp only [CFSG.Sporadic.SmallF2.Native.idRows, Array.getElem_ofFn]
  rw [Nat.one_shiftLeft]
  have : (i : ℕ) < 24 := by simpa [CFSG.Sporadic.SmallF2.Native.idRows] using hi
  calc 2 ^ i < 2 ^ 24 := Nat.pow_lt_pow_right (by norm_num) this
    _ = 16777216 := by norm_num

end CFSG.Sporadic.Co1Block

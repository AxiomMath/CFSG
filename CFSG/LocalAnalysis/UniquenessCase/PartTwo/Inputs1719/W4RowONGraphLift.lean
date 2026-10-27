module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONGraph
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONLiftInv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.ONSchreier CFSG.Sporadic.ONOddCore CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification

theorem on_outer_exists_inv_of_graph
    {γ : MulAut Pv} (hz : γ zP = zP) {A : GL (Fin 3) PSL3Four.F4}
    (hc : ∀ a a' : onL, (a' : Equiv.Perm (Fin N)) =
      ((γ ⟨a, onM_le (onL_le_M a.2)⟩ : Pv) : Equiv.Perm (Fin N)) →
        lToS a' = (LinearFlag.conjAut 3 PSL3Four.F4 A * LinearFlag.dualAut 3 PSL3Four.F4) (lToS a))
    (hA : (LinearFlag.conjAut 3 PSL3Four.F4 A * LinearFlag.dualAut 3 PSL3Four.F4) ^ 2 = 1) :
    ∃ m : Pv, γ m = m⁻¹ ∧ m * zP = zP * m ∧ orderOf m = 7 := by
  obtain ⟨y, hy, hyr⟩ := exists_inv_seven_of_graph A hA
  obtain ⟨l, hl, hlr⟩ := exists_inv_of_central_two_kernel lToS lToS_surjective
    (by rw [ker_lToS]; exact QL_le_center) (by rw [ker_lToS]; exact QL_isPGroup)
    (resL (resM γ hz)) (LinearFlag.conjAut 3 PSL3Four.F4 A *
      LinearFlag.dualAut 3 PSL3Four.F4).toMonoidHom
    (fun a => hc a (resL (resM γ hz) a)
      ((resL_val (resM γ hz) a).trans (resM_val γ hz _)))
    hy (by norm_num : Nat.Prime 7) (by norm_num : (7 : ℕ) ≠ 2) hyr
  refine ⟨toP ⟨l, onL_le_M l.2⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    have hγl : ((γ (toP ⟨l, onL_le_M l.2⟩) : Pv) : Equiv.Perm (Fin N)) =
        ((l⁻¹ : onL) : Equiv.Perm (Fin N)) := by
      rw [← resM_val γ hz (⟨l, onL_le_M l.2⟩ : onM), ← resL_val (resM γ hz) l, hl]
    rw [hγl, Subgroup.coe_inv, Subgroup.coe_inv]
    rfl
  · exact (mem_M_iff_P (x := toP ⟨l, onL_le_M l.2⟩)).1 (onL_le_M l.2)
  · exact (Subgroup.orderOf_mk (l : Equiv.Perm (Fin N)) (onM_le (onL_le_M l.2))).trans
      ((Subgroup.orderOf_coe l).trans hlr)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

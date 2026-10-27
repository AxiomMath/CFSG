module

public import CFSG.Monster.B.TwoA.Base.FrameBase
import all CFSG.Monster.B.TwoA.Base.FrameBase
public import CFSG.Monster.B.TwoA.Base.WAct


public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2

theorem ncard_wOrbit_wFr :
    (wOrbit wFr).ncard = 46575 := by
  have h := ncard_wOrbit_mul wFr
  rw [← Mfr, natCard_Mfr, show (42305421312000 : ℕ) = 46575 * 908328960 by norm_num] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

theorem native_short_frame_stabilizer :
    twoΩCls ∈ vPerpL v0 ∧ wFr ≠ 0 ∧
    (∀ k : Kstab v0, k ∈ Mfr ↔ kOp k twoΩCls = twoΩCls) ∧
    (∀ k : Kstab v0, k ∈ Mfr ↔ ∃ a : C, (a : Fin 24 → ZMod 2) ∈ Ceq ∧ ∃ p ∈ Ppair,
      (k : OLq) = QuotientGroup.mk (gO a * PO p)) ∧
    (∃ e : SDD ceqHyp ≃* Mfr, ∀ (a : Ceq) (p : Ppair),
      ((e ⟨Multiplicative.ofAdd (Submodule.Quotient.mk a), p⟩ : Kstab v0) : OLq) =
        QuotientGroup.mk (gO ⟨a, a.2.1⟩ * PO (p : AutPerm)⁻¹)) ∧
    Nat.card (Ceq ⧸ ΩIn Ceq) = 2 ^ 10 ∧ Nat.card Ppair = 887040 ∧
    Nat.card Mfr = 908328960 ∧ (wOrbit wFr).ncard = 46575 := by
  refine ⟨twoΩCls_mem_vPerpL, wFr_ne_zero, mem_Mfr_iff_fix,
    fun k => (mem_Mfr_iff k).trans (mem_monoSub_iff ceqHyp), ⟨MfrEquiv, fun a p => ?_⟩,
    natCard_Ceq_quot, natCard_Ppair, natCard_Mfr, ncard_wOrbit_wFr⟩
  rw [coe_MfrEquiv, monoD_mk]
  rfl

end CFSG.Monster.B.TwoA

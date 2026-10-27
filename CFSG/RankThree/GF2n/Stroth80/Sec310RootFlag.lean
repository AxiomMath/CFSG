module

public import CFSG.RankThree.GF2n.Stroth80.Ctx
import CFSG.RankThree.GF2n.Stroth80.Sec123Order
import CFSG.RankThree.GF2n.Stroth80.Sec5Main

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.LB_flag (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G))
    {t : G} (ht : t ∈ LB M Q B) (htQ : t ∉ Q) {l : G} (hl : l ∈ LB M Q B) :
    (∀ b ∈ B, ⁅l, b⁆ ∈ Z) ∧
    (∀ v ∈ Vt M (LB M Q B) B Z t ⊓ QB B, ⁅l, v⁆ ∈ B ⊔ Z) ∧
    (∀ v ∈ Vt M (LB M Q B) B Z t, ⁅l, v⁆ ∈ Vt M (LB M Q B) B Z t ⊓ QB B) := by
  have hlR : l ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) ht hl
  have hN : l ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt ht hlR
  have hV := hc.Vt_isElemAbelian h35 ht htQ
  have hcomm : ∀ x ∈ Vt M (LB M Q B) B Z t, ∀ y ∈ Vt M (LB M Q B) B Z t, x * y = y * x := by
    intro x hx y hy
    exact congrArg (fun z : ↥(Vt M (LB M Q B) B Z t) => (z : G))
      (hV.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨fun b hb => hc.comm_B_mem_Z hl hb, fun v hv => ?_, fun v hv => ?_⟩
  · have hvQ : v ∈ Q := hc.Vt_le_Q t (Subgroup.mem_inf.mp hv).1
    rw [sup_comm]
    exact hc.comm_LB_inf_QB_mem_sup hl (Subgroup.mem_inf.mpr ⟨hvQ, (Subgroup.mem_inf.mp hv).2⟩)
  · have hvQ : v ∈ Q := hc.Vt_le_Q t hv
    have hvC : v ∈ Subgroup.centralizer (B : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun h hh =>
        hcomm h (hc.B_le_Vt ht (SetLike.mem_coe.mp hh)) v hv
    have hQB : ⁅l, v⁆ ∈ QB B := (Subgroup.mem_inf.mp (hc.comm_LB_mem_inf hl hvQ hvC)).2
    have hconj : l * v * l⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      SetLike.mem_coe.mp ((Subgroup.mem_normalizer_iff.mp hN v).mp (SetLike.mem_coe.mpr hv))
    have hVc : ⁅l, v⁆ ∈ Vt M (LB M Q B) B Z t := by
      rw [commutatorElement_def]
      exact (Vt M (LB M Q B) B Z t).mul_mem hconj ((Vt M (LB M Q B) B Z t).inv_mem hv)
    exact Subgroup.mem_inf.mpr ⟨hVc, hQB⟩

end CFSG.RankThree.GF2n.Stroth80

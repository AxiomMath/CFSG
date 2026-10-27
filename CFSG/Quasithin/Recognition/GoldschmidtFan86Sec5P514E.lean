module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Ctx
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Lab

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_h (F : FanTree Γ G) {z : G} {α o v : V} (C : LblCtx Γ z α o) (hv : Γ.Adj o v)
    (hne : α ≠ v) : ∃ h : G, h ∈ Gcirc Γ G o v ∧ h ∉ nbrStab Γ G o ∧ Γ.Adj o (h • α) ∧
      h • α ≠ α ∧ h • α ≠ v := by
  obtain ⟨h, hh, hhn⟩ := F.exists_gcirc_not_mem_left hv C.v5
  have hho : h • o = o := MulAction.mem_stabilizer_iff.1 hh.1.1
  have hhv : h • v = v := MulAction.mem_stabilizer_iff.1 hh.1.2
  refine ⟨h, hh, hhn, ?_, fun hα => hhn ?_, fun hα => hne ?_⟩
  · have := (F.adj_smul h o α).2 C.adj.symm
    rwa [hho] at this
  · exact mem_nbrStab.2 fun c hc =>
      F.frobenius_two o α v C.adj.symm hv hne h hh.1.1 hα hhv c hc
  · exact MulAction.injective h (hα.trans hhv.symm)

theorem lab_one_eq (T : Track Γ G) {z : G} {a : ℤ} (hz : z ∈ Cinv G (T.line.vert (a + 1))) :
    lab T z 1 = Lb z (T.line.vert (a + 1)) (T.line.vert (a + 2 + 1)) := by
  have hg : T.τ ^ (1 : ℤ) • T.line.vert (a + 1) = T.line.vert (a + 2 + 1) := by
    rw [T.zpow_smul_vert]
    congr 1
    omega
  rw [Lb_eq hz hg, lab, ← zpow_neg]

end P514

end CFSG.Quasithin.Fan86

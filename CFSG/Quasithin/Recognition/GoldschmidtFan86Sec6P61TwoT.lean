module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61TwoF20
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514E

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P61

open P514

theorem fan61_two_f20 (F : FanTree Γ G) (T : Track Γ G) {z : G} {a : ℤ}
    (hzC : T.line.IsCoreFix z a (a + 2) (a - 2) (a + 4))
    (C : LblCtx Γ z (T.line.vert (a + 1)) (T.line.vert (a + 2)))
    (h4 : (nbrStab Γ G (T.line.vert (a + 2))).relIndex
      (MulAction.stabilizer G (T.line.vert (a + 2)) ⊓
        MulAction.stabilizer G (T.line.vert (a + 1))) = 4) : False := by
  have hz2 : z * z = 1 := C.cinv.2.1
  have ht2 : lab T z (-1) * lab T z (-1) = 1 := lab_mul_self T hz2 (-1)
  have hfixt : ∀ i : ℤ, a - 4 ≤ i → i ≤ a + 2 →
      lab T z (-1) • T.line.vert i = T.line.vert i := fun i h1 h2 =>
    (mem_fixIdx_lab T z (-1) i).2 ((hzC.fix _).2 ⟨by omega, by omega⟩)
  have hK : Lb z (T.line.vert (a + 1)) (T.line.vert (a + 2 + 1)) ∈
      nbrStab Γ G (T.line.vert (a + 1)) := by
    rw [← lab_one_eq T C.cinv]
    refine T.line.mem_nbrStab_of_fix F (u := a + 1) ?_ ?_ ?_
    · exact (mem_fixIdx_lab T z 1 (a + 1 - 1)).2 ((hzC.fix _).2 ⟨by omega, by omega⟩)
    · exact (mem_fixIdx_lab T z 1 (a + 1)).2 ((hzC.fix _).2 ⟨by omega, by omega⟩)
    · exact (mem_fixIdx_lab T z 1 (a + 1 + 1)).2 ((hzC.fix _).2 ⟨by omega, by omega⟩)
  have htK : lab T z (-1) ∉ nbrStab Γ G (T.line.vert (a + 2)) := by
    intro h
    have h1 := mem_nbrStab.1 h (T.line.vert (a + 2 + 1)) (T.line.adj (a + 2))
    have h2 := (hzC.fix _).1 ((mem_fixIdx_lab T z (-1) (a + 2 + 1)).1 h1)
    omega
  have htc : ∀ h : G, h • T.line.vert a = T.line.vert a → h • T.line.vert (a - 1) =
      T.line.vert (a - 1) → h * lab T z (-1) = lab T z (-1) * h := by
    intro h h1 h2
    have hc := (lab_mem_Cen_edgeStab T z (-1) (a + 1)).2
      (hzC.core.2.2.1 (a + 1) (by omega) (by omega))
    rw [show a + 1 + 2 * (-1) = a - 1 by omega] at hc
    refine hc.2 h ⟨MulAction.mem_stabilizer_iff.2 h2, MulAction.mem_stabilizer_iff.2 ?_⟩
    rw [sub_add_cancel]
    exact h1
  have h₃ : Γ.Adj (T.line.vert a) (T.line.vert (a - 1)) := by
    have := (T.line.adj (a - 1)).symm
    rwa [sub_add_cancel] at this
  have hn₂ : T.line.vert (a + 1) ≠ T.line.vert (a - 1) := by
    have := T.line.nb (a - 1)
    rw [show a - 1 + 2 = a + 1 by omega] at this
    exact this.symm
  have hne : T.line.vert (a + 2 + 1) ≠ T.line.vert (a + 1) := by
    have := T.line.nb (a + 1)
    rw [show a + 1 + 2 = a + 2 + 1 by omega] at this
    exact this.symm
  exact r2_f20 F C h4 (T.line.adj (a + 2)) hne hK (T.line.adj a).symm h₃ hn₂ ht2
    (hfixt (a + 2) (by omega) (by omega)) htK (hfixt (a + 1) (by omega) (by omega)) htc

end P61

end CFSG.Quasithin.Fan86

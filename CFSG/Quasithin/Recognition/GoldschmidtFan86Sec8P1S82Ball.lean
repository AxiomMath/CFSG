module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Comm
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Fix

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem fix_ball (F : FanTree Γ G) (h : Fan71c F L) (h512 : Fan512 F L) {i j m : Fin 5}
    (hmi : i ≠ m) (hmj : j ≠ m) (hmid : 2 * m - i = j) {w : V}
    (hw : Γ.dist (D.beta m) w ≤ 3) : (L.z (D.alpha i) * L.z (D.alpha j)) • w = w := by
  have hw' : Γ.dist w (D.beta m) ≤ 3 := by rw [SimpleGraph.dist_comm]; exact hw
  rw [mul_smul]
  rcases IsTree.dist_adj_cases F.isTree (r := w) (D.adj_start_beta m) with h1 | h1
  · rw [D.fix_alpha_side F h j (by omega) hw, D.fix_alpha_side F h i (by omega) hw]
  · have hb : Γ.dist w (D.beta m) + 1 = Γ.dist w α := h1.symm
    have hcases : Γ.dist w (D.beta m) = 0 ∨ Γ.dist w (D.beta m) = 1 ∨
        Γ.dist w (D.beta m) = 2 ∨ Γ.dist w (D.beta m) = 3 := by omega
    rcases hcases with h0 | h0 | h0 | h0
    · rw [D.fix_below_one F h hmj hb (by omega), D.fix_below_one F h hmi hb (by omega)]
    · rw [D.fix_below_one F h hmj hb (by omega), D.fix_below_one F h hmi hb (by omega)]
    · have := D.fix_depth_two F h hmi hmj h0 (by omega)
      rwa [mul_smul] at this
    · have := D.fix_depth_three F h h512 hmi hmid h0 (by omega)
      rwa [mul_smul] at this

end D10Set

theorem fan_8_2c_ball {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h512 : Fan512 F L)
    {α : V} (D : D10Set L α) {i j : Fin 5} (hij : i ≠ j) :
    L.z (D.alpha i) * L.z (D.alpha j) ∈ ballStab Γ G 3 (D.beta (midlab i j)) := by
  obtain ⟨⟨h1, h2, -, -, -, -, -, -, -⟩, ⟨hmid, -⟩, -⟩ := fin5_midlab_facts i j hij
  exact mem_ballStab.2 fun w hw => D.fix_ball F h7.2.2.1 h512 (Ne.symm h1) (Ne.symm h2) hmid hw

end CFSG.Quasithin.Fan86

module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F96Alg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F98Cfg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Card

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {F : FanTree Γ G}
  {L : ZLab Γ G}

theorem fan_9_6a (h7 : Fan7 F L) (h82a : Fan82a F L) (h83b : Fan83b F L) (h83d : Fan83d F L)
    (h85 : Fan85 F L) (h95 : Fan95 F L) : Fan96a F L := by
  intro S
  have h95d : Fan95d F L := h95.2.2.2
  have hR := S.p1Rel_of F h7.2.2.1 h82a h83b h83d h85
  refine ⟨(S.baseIds F h95d).wy_zero hR, fun hsq => ?_, fun hsq => ?_⟩
  · exact (S.e1ids F h95d hsq).wy_two hR
  · exact (S.e0ids F h95d hsq).wy_two hR

theorem fan_9_6b (h7 : Fan7 F L) (h82a : Fan82a F L) (h83b : Fan83b F L) (h83c : Fan83c F L)
    (h83d : Fan83d F L) (h85 : Fan85 F L) (h512 : Fan512 F L) (h95 : Fan95 F L) :
    Fan96b F L := by
  intro S hc4
  have h95d : Fan95d F L := h95.2.2.2
  have hR := S.p1Rel_of F h7.2.2.1 h82a h83b h83d h85
  have hC := S.p1cRel_of F h7.2.2.1 h7.1 h512 h83c hc4
  have hb := S.baseIds F h95d
  have h2 : S.c⁻¹ * S.yMu 2 * S.c = S.yMu 2 * S.zNb 2 := by
    rcases S.isW1.sq with hsq | hsq
    · exact (S.e1ids F h95d hsq).cy_two hR hC
    · exact (S.e0ids F h95d hsq).cy_two hR hC
  refine ⟨hb.cy_zero hR hC, fun i hi => ?_⟩
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by
    clear hi
    revert i
    decide
  rcases hi3 with rfl | rfl | rfl
  · exact absurd rfl hi
  · exact hb.cy_one hR hC h2
  · exact h2

theorem fan_9_6 (h7 : Fan7 F L) (h82a : Fan82a F L) (h83b : Fan83b F L) (h83c : Fan83c F L)
    (h83d : Fan83d F L) (h85 : Fan85 F L) (h512 : Fan512 F L) (h95 : Fan95 F L) : Fan96 F L :=
  ⟨fan_9_6a h7 h82a h83b h83d h85 h95, fan_9_6b h7 h82a h83b h83c h83d h85 h512 h95⟩

end CFSG.Quasithin.Fan86

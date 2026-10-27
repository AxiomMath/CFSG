module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Sup
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt1

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_8_1 {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) : Fan81 F L := by
  obtain ⟨-, h71b, h71c, h72a, -⟩ := h7
  have h40 : Fan40 F := fan40_of_fan71b h71b
  intro α a₀ β δ δ' hα hZ
  obtain ⟨γ, γ', D⟩ := Z2Cfg.of_isZ2Pair F.isTree hZ
  obtain ⟨-, -, -, -, -, -, -, hnot⟩ := hZ
  refine Set.ext fun v => ⟨fun h => ?_, fun hv => ?_⟩
  · exact D.sup_target h71c h72a h40 hα hnot h.1 h.2
  · exact D.sub_target h71c hα hv

end CFSG.Quasithin.Fan86

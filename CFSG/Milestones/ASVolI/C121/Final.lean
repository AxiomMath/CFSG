module

public import CFSG.Milestones.ASVolI.C121.Red3
public import CFSG.Milestones.ASVolI.C121.P4Final

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.LieType.BorelTits

theorem burnsideC121_of
    (h610 : B_6_10) (h123 : I_2_3) : C_1_21 := by
  intro Ω _ _ C₁ C₂ hC X L T R hX hLX hLc hLq hT hSR hRT hQR hRX
  exact ⟨fun Y hY => burnsideC121_part1 h610 h123 hC hX hT hSR hRT hQR hRX hY,
    burnsideC121_part2 h610 h123 hC hX hLX hLc hLq hT hSR hRT hQR hRX,
    burnsideC121_part3 h610 h123 hC hX hLX hLc hLq hT hSR hRT hQR hRX,
    burnsideC121_part4 hX hLX hLc hLq hT hSR hRT hQR hRX⟩

end CFSG.ASVolI

module

public import CFSG.Quasithin.Vol2.GoldschmidtE217NCLin
public import CFSG.Quasithin.Vol2.GoldschmidtE217NCUni
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3TwoD
public import CFSG.Quasithin.Vol2.Ch3E213MOLA9

public section

namespace CFSG.Quasithin

namespace E217R3

theorem kFactL3U3NotOddCube_holds : KFactL3U3NotOddCube := by
  intro K _ _ p hp hp5 hK z hz
  have : Fact p.Prime := ⟨hp⟩
  rcases hK with ⟨-, hU⟩ | ⟨-, hL⟩
  · obtain ⟨F, _, _, _, hcard, θ, hθ, hker⟩ := Ch3E213M.OLA.exists_theta_uni hU
    exact not_oddCube_uni hp5 hcard θ hθ hker hz
  · obtain ⟨θ, hθ, hker⟩ := Ch3E213M.OLA.exists_theta_lin hL
    have hG : Nat.card (GaloisField p 1) = p := by
      rw [GaloisField.card p 1 one_ne_zero, pow_one]
    exact not_oddCube_lin hp5 hG θ hθ hker hz

end E217R3

end CFSG.Quasithin

module

public import CFSG.Milestones.ASVolI.C135.C135
public import CFSG.Milestones.ASVolI.C135.NH

public section

namespace CFSG.ASVolI

open CFSG.Quasithin

theorem burnsideC135_asC135ThreeOne : burnsideC135_AsC135ThreeOne := by
  intro G _ _ G₀ R₀ L F _ _ α hMS hL hG hGL hF hα hcent hnat hdual
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime hF
  obtain ⟨β, βU, H⟩ := burnsideC135_exists_H1 hF hMS hL hG hGL hα hcent hnat hdual
  exact H.pCoreOf_eq

theorem burnsideC135_C_1_35_ofW (h134 : burnsideC135_C134W) : C_1_35 :=
  burnsideC135_C_1_35_of_threeOne h134 burnsideC135_asC135ThreeOne

end CFSG.ASVolI

end

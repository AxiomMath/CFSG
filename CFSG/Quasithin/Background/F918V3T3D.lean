module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.F918V3T3B
public import CFSG.Quasithin.Background.F918V3T3C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Blueprint

theorem three_dvd_card_of_a23List
    {S : Type} [Group S] [Finite S] (h : A23List S)
    (hnsz : ¬ ∃ e : ℕ, IsSz e S) : 3 ∣ Nat.card S := by
  rcases h with ⟨n, h5, h8, ⟨e⟩⟩ | ⟨p, -, -, ⟨f, -, hm⟩ | hm | hm⟩ |
    ⟨⟨f, ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, -, hm⟩ |
      ⟨-, -, hm⟩⟩ | hm⟩ | ⟨n, -, hm⟩ | ⟨s, hs, ⟨e⟩⟩
  · exact F918V3T3.three_dvd_card_alternating h5 h8 e
  · exact F918V3T3.three_dvd_card_of_PSL hm
  · exact F918V3T3.three_dvd_card_of_PSL hm
  · exact F918V3T3.three_dvd_card_of_PSU hm
  · exact F918V3T3.three_dvd_card_of_PSL hm
  · exact F918V3T3.three_dvd_card_of_PSL hm
  · exact F918V3T3.three_dvd_card_of_PSU hm
  · exact F918V3T3.three_dvd_card_of_PSp_two hm
  · exact F918V3T3.three_dvd_card_of_G2 hm
  · exact F918V3T3.three_dvd_card_of_trialityD4 hm
  · exact F918V3T3.three_dvd_card_of_twistedF4 hm
  · exact absurd ⟨f, hm⟩ hnsz
  · exact F918V3T3.three_dvd_card_of_Tits hm
  · exact F918V3T3.three_dvd_card_of_PSL hm
  · exact F918V3T3.three_dvd_card_of_sporadic hs e

end CFSG.Quasithin

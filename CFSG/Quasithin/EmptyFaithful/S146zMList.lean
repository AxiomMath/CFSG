module

public import CFSG.Quasithin.EmptyFaithful.S146zMComp
public import CFSG.Quasithin.EmptyFaithful.S146zMListCl
public import CFSG.Quasithin.EmptyFaithful.S146zMListSp
public import CFSG.Quasithin.EmptyFaithful.S146zMListEx

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem sqtkList3Dvd_proved :
    SQTKList3Dvd := by
  intro S _ _ hS h3
  rcases hS with ⟨n, h5, h8, ⟨e⟩⟩ | ⟨p, hp, hp2, hcl⟩ |
    ⟨⟨f, hA | hB | hC | hD | hE | hF | hG | hH⟩ | hT⟩ | ⟨n, hn, hm⟩ | ⟨s, hs, ⟨e⟩⟩
  · exact absurd (three_dvd_card_alternating h5 h8 e) h3
  · rcases hcl with ⟨f, -, hm⟩ | hm | hm
    · exact absurd (three_dvd_card_psl_model hm) h3
    · exact absurd (three_dvd_card_psl_model hm) h3
    · exact absurd (three_dvd_card_psu_three_model hm) h3
  · exact absurd (three_dvd_card_psl_model hA.2) h3
  · exact absurd (three_dvd_card_psl_model hB.2) h3
  · exact absurd (three_dvd_card_psu_three_model hC.2) h3
  · exact absurd (three_dvd_card_psp_model hD.2) h3
  · exact absurd (three_dvd_card_chevalleyExceptional_model hE.2) h3
  · exact absurd (three_dvd_card_chevalleyExceptional_model hF.2) h3
  · exact absurd (three_dvd_card_twistedF4_model hG.2.2) h3
  · exact ⟨f, hH⟩
  · exact absurd (three_dvd_card_tits_model hT) h3
  · exact absurd (three_dvd_card_psl_model hm) h3
  · rw [Nat.card_congr e.toEquiv] at h3
    exact absurd (three_dvd_card_sporadic hs) h3

end CFSG.Quasithin

module

public import CFSG.Quasithin.Background.ONanE68LieDispatch

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique

theorem e68LieRankTwo_of_facts
    (hF : E68LieFacts)
    (hInn : Ch1.EvenLieAutInner) (h121 : Id2519.Prop121Three) : E68LieRankTwo := by
  intro G _ _ T M V U L hV h hU hL hLie
  rcases hLie with ⟨n, hn, hm⟩ | ⟨n, ho, h3, hm⟩ | ⟨n, hn, hm⟩ | ⟨n, hn, hm⟩ | ⟨n, hn, hm⟩ | hm |
    hc
  · exact out_of_rankOne hF hInn h121 hV h hU hL (Or.inl ⟨hn, hm⟩)
  · exact out_of_rankOne hF hInn h121 hV h hU hL (Or.inr (Or.inl ⟨ho, h3, hm⟩))
  · exact out_of_lin3 hF hInn h121 hV h hU hL hn hm
  · exact out_of_rankOne hF hInn h121 hV h hU hL (Or.inr (Or.inr ⟨hn, hm⟩))
  · exact out_of_sp4 hF hInn h121 hV h hU hL hn hm
  · exact out_of_psl25 hF hInn h121 hV h hU hL hm
  · exact out_of_cover hF hInn h121 hV h hU hL hc

end E68Proof

end E6

end CFSG.Quasithin

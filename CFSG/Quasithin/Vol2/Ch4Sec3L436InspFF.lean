module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspFFG2
public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Insp
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspFFL2
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspFFSmall
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspFFSp4

public section

namespace CFSG.Quasithin.H13.Ch4

theorem inspFF436_of
    (hG2 : InspFFG2) : InspFF436 := by
  intro U _ _ hU2 L K A n p hn hLq hlist hKL hK hAK hA1 hA2 hAcard hoff hp hp2 hpn hcase
  rcases hlist with ⟨m, F, _, _, hF, ⟨e⟩⟩ | ⟨m, F, _, _, hF, ⟨e⟩⟩ | ⟨m, F, _, _, hF, ⟨e⟩⟩ |
    ⟨m, F, _, _, hF, ⟨e⟩⟩ | h6 | h7 | hhat | ⟨F, _, _, hF, ⟨e⟩⟩ | h4 | h5
  · exact FFL2.eq_of_sl2 hU2 hn hF e hKL hK hAK hA1 hA2 hAcard hoff
  · exact (FFL3.false_of_sl3 hn hF e hLq hKL hK hp hp2 hpn hcase).elim
  · exact (FFSp4.false_of_sp4 hn hF e hLq hKL hK hp hp2 hpn hcase).elim
  · exact (FFG2.false_of_g2 hG2 hn hF e hLq hKL hK hp hp2 hpn hcase).elim
  · obtain ⟨e⟩ := h6
    exact (FFSmall.false_of_alt (Or.inl rfl) hn e hKL hK hp hpn hcase).elim
  · obtain ⟨e⟩ := h7
    exact (FFSmall.false_of_alt (Or.inr rfl) hn e hKL hK hp hpn hcase).elim
  · exact (FFSmall.false_of_hat hn hhat hKL hK hp hpn hcase).elim
  · exact (FFSmall.false_of_g2Two hn hF e hKL hK).elim
  · obtain ⟨e⟩ := h4
    exact (FFSmall.false_of_sl4 hn e hKL hK hp hpn hcase).elim
  · obtain ⟨e⟩ := h5
    exact (FFSmall.false_of_sl5 hn e hKL hK hp hpn hcase).elim

end CFSG.Quasithin.H13.Ch4

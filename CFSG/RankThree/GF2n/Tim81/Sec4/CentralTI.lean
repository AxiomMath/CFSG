module

public import CFSG.RankThree.GF2n.Tim81.Sec4.CentralTIL2
public import CFSG.RankThree.GF2n.Tim81.Sec4.CentralTISz
public import CFSG.RankThree.GF2n.Tim81.Sec4.Inputs

public section

namespace CFSG.RankThree.GF2n.Tim81

theorem centralTIStatement :
    CentralTIStatement := by
  intro Y _ _ T Z _ hT hgen hTI hwc hZ hL
  rcases hL with h | h
  · obtain ⟨F, hField, hFintype, hChar, h4, ⟨e⟩⟩ := h
    letI : Field F := hField
    letI : Fintype F := hFintype
    letI : CharP F 2 := hChar
    exact CentralTI.centralTI_sl2 hT hgen hTI hwc hZ h4 e
  · obtain ⟨a, F, hField, hFintype, hChar, ha, hcard, ⟨e⟩⟩ := h
    letI : Field F := hField
    letI : Fintype F := hFintype
    letI : CharP F 2 := hChar
    exact CentralTI.centralTI_sz hT hgen hTI hwc hZ ha hcard e

end CFSG.RankThree.GF2n.Tim81

module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIpIso
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIpData
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIpK1b

public section

namespace CFSG.StandardType.RCKK1IIp

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1

theorem rckRowK1_IIp : RCKRowK1 .IIp (RCKPosCent 96) := by
  intro Jb _ _ hodd hmark
  obtain ⟨e⟩ := rckIIp_iso hmark
  have hdata : RCKK1Data rA8 vA8 := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := rckIIp_A8_four
    exact ⟨h1, h2, h3, h4, h5, rckIIp_A8_K1b⟩
  refine ⟨e.symm rA8, vA8.map e.symm.toMonoidHom, rckK1Data_map e.symm hdata, ?_⟩
  show Nat.card (Subgroup.centralizer ({e.symm rA8} : Set (Jb ⧸ Subgroup.center Jb))) = 96
  rw [rckIIp_card_centralizer_map, card_centralizer_rA8]

end CFSG.StandardType.RCKK1IIp

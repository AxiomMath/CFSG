module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporLat
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatJ3Dc
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.Bridge.J3Surj
public import CFSG.Sporadic.Schreier.PairJ3Faithful
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2236
public import Certificates.Certificate2237
public import Certificates.Certificate2238
public import Certificates.Certificate2239
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2281
public import Certificates.Certificate2283
public import Certificates.Certificate3169
public import Certificates.Certificate8033
public import Certificates.Certificate9119
public import Certificates.Certificate9211
public import Certificates.Certificate10501

public section

namespace CFSG.LocalAnalysis.WeakClosure81


open CFSG.QuasithinUnique.Ch1.SporLat in
theorem asch54SporGenAt_j3 :
    Asch54SporGenAt .J3 := by
  refine asch54SporGenAt_of_list
    (CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv.map fun f =>
      f.symm.trans CFSG.Sporadic.Schreier.j3PermEquiv)
    (fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1)
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    CFSG.Sporadic.SmallOddCore.j3_outer_card_le
    (L := #[1, 3, 3, 9, 15]) (N := 392445) (k := 7) J3K.S_sylow J3K.complete
    (fun j _ => J3K.S_le_Y j) (fun j hj => ?_)
    (by rw [CFSG.Sporadic.Schreier.card_j3P]; norm_num) (a := 4) (b := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [J3K.member_card hj, J3K.card_S]
  norm_num

end CFSG.LocalAnalysis.WeakClosure81

end

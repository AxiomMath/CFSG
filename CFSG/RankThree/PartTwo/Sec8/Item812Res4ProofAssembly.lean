module

public import CFSG.RankThree.PartTwo.Sec8.Item812ProofFinal
public import CFSG.RankThree.PartTwo.Sec8.Item812Proof89G2
public import CFSG.RankThree.PartTwo.Sec8.Item812Proof810
public import CFSG.RankThree.PartTwo.Sec8.Item812Proof811
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofXNormal
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofCenter
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofRee
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofD4
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGen
public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofOmega
public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofSU
public import CFSG.RankThree.PartTwo.Sec8.Item812Proof89
public import CFSG.RankThree.PartTwo.Sec13.Item138N
public import CFSG.RankThree.PartTwo.Sec4.Statements417
public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofFrattini
public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofSylow
public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofSUInner
public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofSpReal
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofChoice
public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofFusion
public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofLocal
public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofApply
public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofConfig
import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
import CFSG.RankThree.PartTwo.KFacts.K71Item89
import CFSG.RankThree.PartTwo.KFacts.K71Sp4
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
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
public import Certificates.Certificate76
public import Certificates.Certificate77

public section

namespace CFSG.RankThree.PartTwo.Sec8

theorem fin812Sylow_of_res4 (hPa : Fin812PaSplit) (hBq : Fin812BEq) (hQR : Fin812QR)
    (hBw : Fin812BWeak) (hW : KF812WreathCent) (hF : KF812E27Fuse) : Fin812Sylow :=
  fin812Sylow_of (fin812Local_of hPa hBq hQR hBw hW) (fin812FusionW_of hW)
    (fin812FusionV_of_kf hF hW) (fin812Extremal_of_kf hW)

theorem sec8Never_of_xy (h87 : Item87) (h88 : Item88) (h84 : Pair84A) (hsym : Pair84Sym)
    (hXY : Item89XY) (hcfg : Pair89InConfig) (hS : Fin812Sylow) : Sec8Never := by
  have h89 := item89_of_split h88 hXY (pair89Omega_of hXY h87 h84 hcfg)
  exact sec8Never_of h87 h88 h89 (item810_of h87 h89 pair810Center)
    (item811_of h87 h89 hsym (pair811Gen_of pair811GenSU)) hS fin812Frattini fin812XNormal h84

end CFSG.RankThree.PartTwo.Sec8

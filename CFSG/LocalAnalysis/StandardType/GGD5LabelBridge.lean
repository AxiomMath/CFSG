module

public import CFSG.LocalAnalysis.StandardType.GGD5Inputs
public import Certificates.Certificate43
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
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate10010
public import Certificates.Certificate10011
public import Certificates.Certificate13604
public import Certificates.Certificate13657
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGD5LabelL
import CFSG.LocalAnalysis.StandardType.GGD5LabelJ
import CFSG.LocalAnalysis.StandardType.GGD5LabelAJ
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

theorem ggD5LabelDataInput_holds :
    GGD5LabelDataInput := by
  intro G _ _ p B Bs x L D J hS hp _ hxL _ y K hnb M e hecart he0 hb2 _ hbas
  have hD4 := lup10d_label_L hS hp hxL M e hecart he0 hbas
  obtain ⟨hlabJ, hJaut⟩ := lup10d_omegaEnd hS hp M e hbas hD4
  have hcore := lup10d_labelCore_of_labelJ hS hp hlabJ
  exact ⟨hcore.1, hcore.2.1,
    lup10d_labelAJ_of_fix hS hp hnb M e hecart he0 hb2 hbas hJaut, hcore.2.2⟩

end CFSG.StandardType

end

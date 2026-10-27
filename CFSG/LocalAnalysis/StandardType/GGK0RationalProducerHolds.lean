module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGK0ProducerAssembly
import CFSG.LocalAnalysis.StandardType.GGK0LangMarkUntw
import CFSG.LocalAnalysis.StandardType.GGK0LangMarkTw
import CFSG.LocalAnalysis.StandardType.GGK0LQAlgClosure

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG.Assembly CFSG.StandardType

theorem f4Producer_holds :
    RationalProducerOn (AlgebraicClosure (ZMod 2)) .F4 :=
  rationalProducerOn_of_langMark GGK0LQ.hAlg_algebraicClosure
    (k0LangMark_hA_untw (Or.inl rfl))

theorem e6Producer_holds :
    RationalProducerOn (AlgebraicClosure (ZMod 2)) .E6 :=
  rationalProducerOn_of_langMark GGK0LQ.hAlg_algebraicClosure
    (k0LangMark_hA_untw (Or.inr (Or.inl rfl)))

theorem twE6Producer_holds :
    RationalProducerOn (AlgebraicClosure (ZMod 2)) .twE6 :=
  rationalProducerOn_of_langMark GGK0LQ.hAlg_algebraicClosure k0LangMark_hA_tw

theorem e7Producer_holds :
    RationalProducerOn (AlgebraicClosure (ZMod 2)) .E7 :=
  rationalProducerOn_of_langMark GGK0LQ.hAlg_algebraicClosure
    (k0LangMark_hA_untw (Or.inr (Or.inr (Or.inl rfl))))

theorem e8Producer_holds :
    RationalProducerOn (AlgebraicClosure (ZMod 2)) .E8 :=
  rationalProducerOn_of_langMark GGK0LQ.hAlg_algebraicClosure
    (k0LangMark_hA_untw (Or.inr (Or.inr (Or.inr rfl))))

end CFSG.StandardType.GGK0MarkedKacIface1587

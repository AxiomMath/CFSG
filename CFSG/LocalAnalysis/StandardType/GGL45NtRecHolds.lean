module

public import CFSG.LocalAnalysis.StandardType.GGL45NtRecLin
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecUni
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecSp
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecOrth
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecE6
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecExU
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecTwE6
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecExTw

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45NtRecOn_cl :
    GGL45NtRecOn GGL45NtFamCl :=
  (ggL45NtRecOn_lin.union (ggL45NtRecOn_uni.union (ggL45NtRecOn_sp.union
    ggL45NtRecOn_orth))).antitone ggL45NtFamCl_cover

theorem ggL45NtRecOn_ex :
    GGL45NtRecOn GGL45NtFamEx :=
  (ggL45NtRecOn_exU.union (ggL45NtRecOn_e6.union (ggL45NtRecOn_twE6.union
    ggL45NtRecOn_exTw))).antitone ggL45NtFamEx_cover

end CFSG.StandardType

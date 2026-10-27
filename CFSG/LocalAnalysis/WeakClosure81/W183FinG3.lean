module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinA5
public import CFSG.LocalAnalysis.WeakClosure81.W183FinA6
public import CFSG.LocalAnalysis.WeakClosure81.W183FinU34
public import CFSG.LocalAnalysis.WeakClosure81.W183FinG3L34
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44G3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem finG3_holds :
    FinG3 := by
  intro Y _ _ L hLn hC A hcard hel hTI1
  refine ⟨?_, ?_⟩
  · rintro (hL2 | hL3 | hU3 | hSp)
    · exact finG3A5_holds Y L hLn hL2 hC A hcard hel hTI1
    · exact finG3L34_holds Y L hLn hL3 hC A hcard hel hTI1
    · exact finG3U34_holds Y L hLn hU3 hC A hcard hel hTI1
    · exact finG3Sp44_holds Y L hLn hSp hC A hcard hel hTI1
  · rintro (h | h)
    · exact finG3L32_holds Y L hLn h hC A hcard hel hTI1
    · exact finG3A6_holds Y L hLn hC h A hcard hel hTI1

end CFSG.LocalAnalysis.WeakClosure81

end

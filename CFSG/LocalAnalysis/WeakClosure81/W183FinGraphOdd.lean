module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoDyn
public import CFSG.LocalAnalysis.WeakClosure81.W183FinA6
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44GraphOdd

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem finGraphOdd_holds : FinGraphOdd := by
  intro Y _ _ L hLn h hC hτ a ha
  rcases h with h | h
  · exact finGraphOddA6_holds Y L hLn h hC hτ a ha
  · exact finGraphOddSp44_holds Y L hLn h hC hτ a ha

end CFSG.LocalAnalysis.WeakClosure81

end

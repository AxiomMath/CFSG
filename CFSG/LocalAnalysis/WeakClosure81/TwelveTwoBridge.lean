module

public import CFSG.LocalAnalysis.WeakClosure81.EightFourteenTwelveTwo
public import CFSG.LocalAnalysis.WeakClosure81.TwelveTwo
public import CFSG.LocalAnalysis.WeakClosure81.TwelveTwoD
public import CFSG.LocalAnalysis.WeakClosure81.W15Inputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem w3Lem122One_holds (hNat : NatSumL2Input)
    (hMart : CFSG.RankThree.GF2n.MartineauSzInput) : W3Lem122One :=
  fun ρ B Z A n m hS hmin => twelveTwo_one_top hNat hMart ρ B Z A n m hS hmin

theorem w3Lem122Two_holds : W3Lem122Two :=
  fun ρ B Z A n m hS hmin hZ => twelveTwo_two_top ρ B Z A n m hS hmin hZ

end CFSG.LocalAnalysis.WeakClosure81

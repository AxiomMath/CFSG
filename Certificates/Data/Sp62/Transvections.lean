module

public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoCertInputs

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U

@[expose] def sp62X2OK : Bool :=
  orbit0.all fun a => orbit0.all fun b =>
    !commutes6 a b || a == b || found orbit2 (indexMap orbit2) (mul6 a b)

end CFSG.Quasithin.H13.U3

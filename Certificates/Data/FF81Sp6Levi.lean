module

public import Certificates.Data.Item434SmallTwoIII

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Levi

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

@[expose] def leviPred (y : List ℕ) : Bool :=
  ((List.range 3).any fun a => (List.range 3).any fun b =>
      mul6 y (zCode 0) == mul6 (vecCode a b 0) y) &&
    (List.range 3).any fun a => (List.range 3).any fun b =>
      mul6 y (zCode 1) == mul6 (vecCode a b 0) y

@[expose] def leviCheck : Bool :=
  allCheck leviPred (closureT ((centGens 3).map Prod.fst)) &&
    allCheck leviPred (closureT ((centGens 4).map Prod.fst))

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Levi

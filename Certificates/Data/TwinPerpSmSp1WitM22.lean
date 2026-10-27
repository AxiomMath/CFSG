module

public import Certificates.Data.TwinPerpSmSp1Wit
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16M22Data
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16Check

public section

namespace Certificates.TwinPerpSmSp1

@[expose] def m22Wit : Q8WitData where
  syl := CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Check.m22Q16
  xg := #[
    #[0, 1, 2, 7, 5, 4, 6, 3, 12, 8, 23, 19, 13, 9, 22, 18, 17, 21, 10, 14, 16, 20, 11, 15],
    #[0, 1, 2, 9, 5, 17, 15, 23, 8, 11, 10, 3, 7, 18, 13, 22, 20, 4, 14, 19, 21, 16, 6, 12],
    #[0, 1, 2, 14, 21, 17, 10, 7, 23, 18, 11, 6, 12, 13, 15, 3, 5, 16, 22, 8, 4, 20, 9, 19],
    #[0, 1, 18, 12, 22, 8, 6, 3, 15, 11, 9, 19, 23, 13, 21, 17, 2, 5, 20, 10, 16, 14, 4, 7]]
  cW := #[[0], [1], [2], [3]]

end Certificates.TwinPerpSmSp1

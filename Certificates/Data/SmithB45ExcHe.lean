module

public import Certificates.Data.CFSGNative.SectionRank.HeLocal

public section

namespace CFSG.Quasithin.B45Exc

open CFSG.SectionRank.Native

@[expose] def heInvData : CubData where
  seedA := heSylow7Data.seedA
  seedB := heSylow7Data.seedB
  nregs := 30
  prog := heSylow7Data.prog ++ [
      .pow 6 1 25, .mul 0 1 26, .mul 26 0 26, .mul 26 1 26, .mul 26 0 26, .mul 26 1 26,
      .mul 26 0 26, .mul 26 25 26, .mul 26 0 26, .mul 26 1 26, .mul 26 0 26, .mul 26 25 26,
      .mul 26 0 26, .mul 26 25 26, .mul 26 0 26, .mul 26 25 26, .mul 26 0 26, .mul 26 1 26,
      .mul 26 0 26, .mul 26 25 26, .mul 26 0 26, .mul 26 25 26, .mul 26 0 26, .mul 26 25 26,
      .pow 7 26 27, .pow 6 23 28, .mul 28 24 29]
  rx := 29
  ry := 23
  rh := 27
  r := 7
  oh := 2
  a := 1
  b := 0
  c := 6
  d := 6
  k := 0
  l := 3
  μ := 6
  t := 0

end CFSG.Quasithin.B45Exc

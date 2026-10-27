module

public import Certificates.Data.CFSGNative.SectionRank.Local
public import Certificates.Data.CFSGNative.SectionRank.F2Fast

public section

namespace CFSG.SectionRank.Native

@[expose] def bMultSeven (_ : Unit := ()) : SqData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/BG1-f2r4370B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/BG1-f2r4370B0.m2"
  nregs := 8
  prog := [.mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 4, .mul 4 4 4, .mul 4 4 5,
      .mul 4 5 4, .mul 5 4 5, .mul 3 3 4, .mul 4 4 4, .mul 4 4 4, .mul 4 4 4,
      .mul 3 4 3, .pow 54 3 4, .mul 4 1 4, .mul 4 3 4, .mul 2 2 3, .mul 2 3 3,
      .mul 3 3 3, .mul 3 3 3, .mul 2 3 2, .pow 54 2 3, .mul 3 5 3, .mul 3 2 3,
      .mul 3 4 3, .mul 3 4 2, .pow 4 3 5, .mul 5 2 5, .pow 8 2 6, .mul 6 2 2,
      .mul 3 3 7, .mul 6 7 6, .pow 5 3 3, .mul 3 3 7, .mul 3 6 3, .mul 7 2 7,
      .pow 5 5 5, .pow 17 3 2, .mul 4 3 4, .mul 2 4 2, .pow 3 7 4, .mul 5 7 5,
      .mul 4 5 4, .pow 2 2 5, .mul 4 5 5, .pow 2 4 7, .mul 5 7 5, .mul 5 2 5,
      .mul 5 4 5, .mul 2 4 7, .pow 2 2 3, .mul 7 3 7, .pow 2 4 3, .mul 7 3 7,
      .mul 7 2 7, .mul 7 4 7, .pow 2 2 4, .mul 7 4 7]
  rx := 5
  ry := 7
  rh := 2
  r := 7
  oh := 3
  a := 0
  b := 3
  c := 1
  d := 5
  t := 0

end CFSG.SectionRank.Native

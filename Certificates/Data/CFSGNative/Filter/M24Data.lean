module

public import Certificates.Data.CFSGNative.Filter.PermSec

public section

namespace CFSG.SectionRank.Native

@[expose] def m24Perm (_ : Unit := ()) : PermData where
  seedA := #[3, 6, 16, 0, 12, 8, 1, 14, 5, 18, 17, 20, 4, 15, 7, 13, 2, 10, 9, 23, 11, 22, 21, 19]
  seedB := #[3, 20, 8, 5, 17, 0, 6, 7, 14, 4, 10, 11, 16, 1, 2, 12, 15, 9, 23, 19, 13, 21, 18, 22]
  nregs := 25
  prog := [
      .mul 1 0 2, .mul 1 2 3, .mul 3 2 4, .mul 4 2 5, .pow 7 2 6, .pow 11 4 7, .mul 7 6 8,
      .pow 3 5 9, .pow 11 8 10, .mul 9 10 11, .mul 8 11 12, .mul 12 0 13, .pow 3 12 14,
      .mul 12 13 15, .pow 6 15 16, .mul 16 14 17, .mul 12 17 18, .mul 18 0 19, .mul 0 19 20,
      .mul 20 14 21, .mul 12 21 22, .mul 22 0 23, .mul 0 23 24]
  outs := [16, 18, 20, 22, 24]

end CFSG.SectionRank.Native

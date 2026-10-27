module

public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Mathieu.M22
public import Certificates.Data.CFSGNative.Mathieu.Check
public import CFSG.Quasithin.Background.HMathieuNorm
public import CFSG.Quasithin.Background.A3ComponentsBasic
public meta import Certificates.Data.CFSGNative.Mathieu.Check
public meta import CFSG.Quasithin.Background.HMathieuCent
public meta import CFSG.Monster.Code.Basis
public import Certificates.Kernel.J4Count.Suborb

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Mathieu.Native
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

open scoped commutatorElement

@[expose] def m21Data : Data where
  tA := #[4, 2, 1, 3, 0, 17, 13, 12, 8, 18, 14, 11, 7, 6, 10, 15, 19, 5, 9, 16, 20]
  tB := #[14, 20, 12, 2, 6, 5, 10, 17, 3, 8, 19, 1, 9, 18, 11, 4, 7, 13, 16, 15, 0]
  words := #[[1], [2], [4, 3, -4], [-3, 5, 3], [-4, -3, 4, 4, 3], [-7, -7, 6, 5, 7], [-6, 8, 6]]
  base := #[0, 1, 5, 2]
  sizes := [21, 20, 16, 3]
  k := 2
  pX := 2
  eX := 0
  pY := 5
  eY := 0
  pXY := 7
  eXY := 0

@[expose] def m21AArr : Array ℕ :=
  #[0, 1, 2, 7, 5, 4, 6, 3, 20, 16, 15, 11, 21, 17, 14, 10, 9, 13, 18, 22, 8, 12, 19, 23]

@[expose] def m21BArr : Array ℕ :=
  #[0, 1, 2, 17, 23, 15, 5, 9, 8, 13, 20, 6, 11, 22, 4, 12, 21, 14, 7, 10, 16, 19, 18, 3]

end CFSG.Quasithin.H.Mathieu

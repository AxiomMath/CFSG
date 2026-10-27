module

public import Certificates.Data.HSOverWords
public import Certificates.Data.HSFiveLocalP

public section

namespace Certificates.HSU35

open CFSG.PSL3Four.Native Certificates.MaxD2Perm

@[expose] def xyU0W : List Int := [1, -2, 1, -2, 1, -2, -1, -2, -1, 2, 1, 1]

@[expose] def xyV0W : List Int := [-2, -1, 2, 1, -2, 1, -2, -1, -2, 1]

@[expose] def xyTW : List Int := [-2, 1, 2, 1, 2, 1, 2, -1, -1, 2, 1, 2]

@[expose] def xyWW : List Int := [-2, 1, 2, 1, -2, 1, 1, 2, -1, 2, 1, 1]

@[expose] def xyCW : List Int := [-1, -1, 2, 1, 1, 1, 2, -1, 2, -1, -2, -1]

@[expose] def xyE1W : List Int := [-1, -2, 1, -2, 1, 1, 2, -1, -1, 2, -1, 2, 1]

@[expose] def xyE2W : List Int := [1, 2, 1, 2, -1, 2, -1, 2, -1, -1, 2, 1, 1]

@[expose] def fourXW : List Int := [2, 2, -4, -3, -2, -4, 3, 2]

@[expose] def fourYW : List Int := [3, 3, -2, -4, -3, -2]

@[expose] def uaXW : List Int := [5, -4, -5, 1, -3]

@[expose] def uaYW : List Int := [3, 1, 4, -5, -3, 4, 1]

@[expose] def uWords : List (List Int) :=
  [Certificates.HSOver.hsOverXW, Certificates.HSOver.hsOverYW]

@[expose, reducible] def dataU : Certificates.MaxD2Perm.Data where
  n := 100
  p := 5
  gT := (uWords.map (wT Certificates.MaxD2Heis.hsFiveDataP)).toArray
  gOrder := 126000
  uW := xyU0W
  vW := xyV0W
  nW := [xyU0W, xyV0W, xyTW]
  nOrder := 1000
  fpPts := List.range 100
  repW := [xyWW]
  genW := [[fourXW, fourYW]]
  tW := xyTW
  tm := 2
  tlam := 2
  te := 4

end Certificates.HSU35

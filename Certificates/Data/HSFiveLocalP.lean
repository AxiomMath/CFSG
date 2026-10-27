module

public import Certificates.Data.HSFiveTables
public import Certificates.Data.HSFiveCheck

public section

namespace Certificates.MaxD2Heis

@[expose] def hsFiveUW : List Int :=
  [-1, -2, -2, -2, -1, -2, -2, -2, -2, -1, -2, -2, -1, -2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2,
    1]
@[expose] def hsFiveVW : List Int :=
  [-1, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, -2, -1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1,
    2, 2, 2, 1]
@[expose] def hsFiveSW : List Int :=
  [-1, -2, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -2, -1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1,
    2, 2, 1, 2, 1]
@[expose] def hsFiveTW : List Int :=
  [1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1]
@[expose] def hsFiveDataP : Certificates.MaxD2Perm.Data where
  n := 100
  p := 5
  gT := #[hsTabA, hsTabB]
  gOrder := 44352000
  nOrder := 2000
  fpPts := []
  uW := hsFiveUW
  vW := hsFiveVW
  nW := [hsFiveUW, hsFiveVW, hsFiveTW, hsFiveSW]
  repW := []
  genW := []
  tW := hsFiveTW
  tm := 2
  tlam := 3
  te := 12

end Certificates.MaxD2Heis

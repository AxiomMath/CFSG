module

public import Certificates.Data.HSFiveLocalP

public section

namespace Certificates.MaxD2Heis

@[expose] def hsFiveS2W : List Int :=
  [-3, -2, -3, -2, -3, 2, 2, 2, 3, 2, 3]
@[expose] def hsFiveDataR : Certificates.MaxD2Perm.Data where
  n := 100
  p := 5
  gT := #[hsTabA, hsTabB, hsTabU]
  gOrder := 88704000
  nOrder := 4000
  fpPts := []
  uW := hsFiveUW
  vW := hsFiveVW
  nW := [hsFiveUW, hsFiveVW, hsFiveTW, hsFiveSW, hsFiveS2W]
  repW := []
  genW := []
  tW := hsFiveTW
  tm := 2
  tlam := 3
  te := 12

end Certificates.MaxD2Heis

module

public import Certificates.Data.MaxD2Perm

public section

namespace Certificates.MaxD2Perm

@[expose] def m11ThreeData : Data where
  n := 11
  p := 3
  gT := #[#[0, 9, 2, 10, 6, 5, 4, 8, 7, 1, 3], #[3, 4, 7, 2, 5, 8, 6, 0, 1, 9, 10]]
  gOrder := 7920
  nOrder := 144
  fpPts := [0, 1, 2, 3]
  uW := [-2, 1, 2, 2, 1, -2, 1, 2, 2]
  vW := [2, 2, 1, -2, 1, 2, 1, -2, 1, -2]
  nW := [[-2, 1, 2, 2, 1, -2, 1, 2, 2], [2, 2, 1, -2, 1, 2, 1, -2, 1, -2], [2, 1, -2],
    [2, 2, 1, 2, 2], [-2, 1, -2, 1, 2]]
  repW := [[1], [2]]
  genW := [
    [[6], [2, 6, 3, 6, 4, 5, 3]],
    [[6, 1, 6, 3, 4], [6]]]
  tW := [-2, 1, -2, 1, 2, 2, 1, -2]
  tm := 4
  tlam := 2
  te := 12

end Certificates.MaxD2Perm

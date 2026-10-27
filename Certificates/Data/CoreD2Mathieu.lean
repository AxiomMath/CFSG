module

public import Certificates.Data.CoreD2Perm

public section

namespace Certificates.CoreD2Perm

open CFSG.PSL3Four.Native
open Certificates.FusD2Perm (powT wordT)

@[expose] def pairOKZ (D : Data) (q : Nat × Nat) : Bool :=
  if q.1 == q.2 then
    decide (q.1 < D.eW.length) && powT D.n (eT D q.1) D.p == idTab D.n &&
      !(eT D q.1 == idTab D.n) &&
      allBelow D.eW.length fun k => comp D.n (eT D q.1) (eT D k) == comp D.n (eT D k) (eT D q.1)
  else pairOK D q

@[expose] def checkZ (D : Data) : Bool :=
  D.eK == 3 &&
    (anyBelow D.eW.length fun i => anyBelow D.eW.length fun j =>
      !(comp D.n (eT D i) (eT D j) == comp D.n (eT D j) (eT D i))) &&
    (allBelow 2 fun j =>
      (giT D)[j]!.size == D.n && comp D.n (giT D)[j]! (gsT D)[j]! == idTab D.n) &&
    (allBelow (gT D).size fun j =>
      (gTi D)[j]!.size == D.n && comp D.n (gTi D)[j]! (gT D)[j]! == idTab D.n) &&
    enumOK D.n (eGens D) (eEnum D) && (eEnum D).tabs.size == D.p ^ D.eK &&
    D.pairs.all (pairOKZ D) && D.fd.length == D.gWs.length && fusOK D &&
    wordT D.n (gT D) (gTi D) D.wA == D.aT && wordT D.n (gT D) (gTi D) D.wB == D.bT

@[expose] def m12CoreData : Data where
  n := 12
  p := 3
  aT := #[3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5]
  bT := #[7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10]
  eW := [[1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2],
    [1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2],
    [1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2]]
  eK := 3
  pairs := [(0, 1), (0, 2)]
  gWs := [[2],
    [1, 2, 1]]
  fd := [⟨0, 0, 1, 2, 2⟩, ⟨1, 0, 2, 1, 2⟩]
  wA := [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1]
  wB := [1]

@[expose] def m24CoreData : Data where
  n := 24
  p := 3
  aT := #[3, 6, 16, 0, 12, 8, 1, 14, 5, 18, 17, 20, 4, 15, 7, 13, 2, 10, 9, 23, 11, 22, 21, 19]
  bT := #[3, 20, 8, 5, 17, 0, 6, 7, 14, 4, 10, 11, 16, 1, 2, 12, 15, 9, 23, 19, 13, 21, 18, 22]
  eW := [[2],
    [1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2,
     1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1],
    [1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2,
     1, 2, 1, -2, 1, 2, 1, -2, 1]]
  eK := 3
  pairs := [(0, 1), (0, 0)]
  gWs := [[2],
    [1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1,
     2, 1, -2, 1, 2, 1, -2, 1],
    [1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1]]
  fd := [⟨1, 1, 0, 1, 0⟩, ⟨0, 1, 1, 2, 1⟩, ⟨1, 1, 0, 1, 0⟩]
  wA := [-2, -3, -2, 3, 2, -1, -3, -2, -3, -3, -2, 3, 3, 2, 2, 3, -1]
  wB := [1]

end Certificates.CoreD2Perm

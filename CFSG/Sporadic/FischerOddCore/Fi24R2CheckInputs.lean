module

public import CFSG.Sporadic.FischerOddCore.Fi24WitCheck
public import CFSG.Sporadic.FischerOddCore.Fi24R2Data
public meta import CFSG.Sporadic.FischerOddCore.Fi24WitCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi24R2Data
public import Certificates.Certificate2078Base
public meta import Certificates.Certificate2078Base
public import Certificates.Kernel.Sporadic.Fi24OrbL.Facts
public meta import Certificates.Kernel.Sporadic.Fi24OrbL.Facts

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi24.Native

@[expose] def fi24PosT (F : Array Nat) : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate nPts F.size
  for j in [0:F.size] do
    r := r.set! F[j]! j
  return r

@[noinline, expose] def fi24R2Checks (O : Enum) (F a b : Array Nat) : Bool :=
  let L := chainLetters O
  let M0 := wordT nPts (letterJ L) localWords[0]!
  let M1 := wordT nPts (letterJ L) localWords[1]!
  let gT := fi24GenT M0 (invT nPts M0) M1 (invT nPts M1)
  let D := powT nPts 7 (wordT nPts gT CFSG.Sporadic.Fi23.Native.dLetters)
  let W := wordT nPts gT fi23WordW
  let U2 := compT nPts D (compT nPts M0 (compT nPts D (invT nPts M0)))
  let U3 := compT nPts U2 (compT nPts W (compT nPts D (invT nPts W)))
  let Ga := wordT nPts (letterJ L) fi24BrayWordA
  let Gb := wordT nPts (letterJ L) fi24BrayWordB
  let Ca := fi24BrayT U3 Ga (invT nPts Ga) fi24BrayExpA true
  let Cb := fi24BrayT U3 Gb (invT nPts Gb) fi24BrayExpB true
  let pos := fi24PosT F
  F.size == 504 && allIn 0 503 (fun j => decide (F[j]! < F[j + 1]!)) &&
    decide (F[503]! < nPts) && allIn 0 504 (fun j => ap U3 F[j]! == F[j]!) &&
    allIn 0 nPts (fun i => ap U3 i != i || (decide (pos[i]! < 504) && F[pos[i]!]! == i)) &&
    invOK nPts Ga (invT nPts Ga) && invOK nPts Gb (invT nPts Gb) &&
    compT nPts Ca U3 == compT nPts U3 Ca && compT nPts Cb U3 == compT nPts U3 Cb &&
    allIn 0 504 (fun j => ap Ca F[j]! == F[a[j]!]!) &&
    allIn 0 504 (fun j => ap Cb F[j]! == F[b[j]!]!)

end CFSG.Sporadic.FischerOddCore

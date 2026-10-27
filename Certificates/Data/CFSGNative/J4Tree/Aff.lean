module

public import Certificates.Data.CFSGNative.J4.Cert
public import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.J4Tree.Native

open CFSG.Sporadic.J4.Native

set_option compiler.extract_closed false

structure Code where
  rows : Array Nat
deriving Inhabited, DecidableEq, Hashable, Repr

namespace Code

@[inline, expose] def mul (a b : Code) : Code :=
  ⟨CFSG.Sporadic.SmallF2.Native.mulRows 12 a.rows b.rows⟩

@[expose] def one : Code := ⟨#[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]⟩

instance : Mul Code := ⟨mul⟩

instance : One Code := ⟨one⟩

@[expose] def inE (a : Code) : Bool :=
  (List.range 11).all fun i => a.rows[i + 1]?.getD 0 == 2 ^ (i + 1)

@[expose] def transl (a : Code) : Nat := (a.rows[0]?.getD 0) >>> 1

@[expose] def wf (a : Code) : Bool := a.rows.size == 12 && a.rows.toList.all (· < 4096)

@[expose] def affShape (a : Code) : Bool :=
  a.rows.size == 12 && (a.rows[0]?.getD 0) % 2 == 1 &&
    (List.range 11).all fun i => (a.rows[i + 1]?.getD 0) % 2 == 0

@[expose] def inv (a : Code) : Code := Id.run do
  let mut m := a.rows
  let mut r := one.rows
  for c in [0:12] do
    let mut p := 12
    for i in [c:12] do
      if p == 12 && (m[i]?.getD 0).testBit c then p := i
    if p < 12 then
      let mc := m[p]?.getD 0
      let rc := r[p]?.getD 0
      m := (m.set! p (m[c]?.getD 0)).set! c mc
      r := (r.set! p (r[c]?.getD 0)).set! c rc
      for i in [0:12] do
        if i != c && (m[i]?.getD 0).testBit c then
          m := m.set! i ((m[i]?.getD 0) ^^^ mc)
          r := r.set! i ((r[i]?.getD 0) ^^^ rc)
  return ⟨r⟩

end Code

@[expose] def projP : Array Nat := #[
    1, 4, 8, 19, 32, 64, 128, 259, 512, 1024, 478, 1350, 145, 1604, 25, 575, 643, 2051, 833, 3027,
    45, 2532, 873, 3289, 3997, 1140, 3623, 2939, 2378, 520, 3496, 973, 2303, 282, 3210, 211, 627,
    1532, 1154, 3893, 3427, 4070, 742, 1910, 2118, 2174, 959, 444, 2289, 1754, 3039, 2171, 2732,
    2263, 3510, 738, 1818, 3564, 3380, 3215, 3377, 2728, 1895, 2103, 4026, 2183, 3630, 2523, 1893,
    1626, 3394, 19, 0, 2730, 2587, 1141, 630, 985, 469, 3527, 1723, 1403, 368, 3511, 1726, 3331,
    3278, 2171, 2927, 2768, 3323, 2198, 306, 40, 2025, 1323, 356, 2821, 1467, 3905, 796, 333, 1533,
    3946, 1489, 3623, 1788, 1921, 2601, 3, 3102, 2058]

@[expose] def secCb : Array V2 := #[
    ⟨1, 0⟩,
    ⟨1, 35184372088832⟩,
    ⟨2, 0⟩,
    ⟨4, 0⟩,
    ⟨8, 35184372088832⟩,
    ⟨16, 0⟩,
    ⟨32, 0⟩,
    ⟨64, 0⟩,
    ⟨128, 35184372088832⟩,
    ⟨256, 0⟩,
    ⟨512, 0⟩,
    ⟨131072, 35184372088832⟩]

@[expose] def proj12 (v : V2) : Nat :=
  (List.range 112).foldl (fun acc j => if v.testBit j then acc ^^^ (projP[j]?.getD 0) else acc) 0

@[expose] def rho12 (M : Array V2) : Code :=
  let t := frTable M
  ⟨secCb.map fun c => proj12 (frApply t c)⟩

@[expose] def compatOK (M : Array V2) : Bool :=
  let R := rho12 M
  (List.range 112).all fun i =>
    proj12 (M[i]?.getD V2.zero) == CFSG.Sporadic.SmallF2.Native.vecMulN 12 R.rows (projP[i]?.getD 0)

@[expose] def secOK : Bool :=
  secCb.size == 12 && (List.range 12).all fun r => proj12 (secCb[r]?.getD V2.zero) == 1 <<< r

@[expose] def xCode : Array Code := #[
    ⟨#[2825, 4054, 1066, 1296, 1868, 1506, 3054, 716, 1866, 1294, 2314, 328]⟩,
    ⟨#[1889, 1450, 2342, 1556, 80, 336, 2552, 2284, 240, 1204, 1648, 2158]⟩,
    ⟨#[603, 1012, 1320, 2292, 1672, 2230, 2438, 4030, 368, 3774, 2334, 792]⟩]

@[expose] def xiCode : Array Code := #[
    ⟨#[319, 2298, 2538, 2980, 2236, 3940, 1838, 2084, 1162, 3524, 3134, 980]⟩,
    ⟨#[943, 3448, 1902, 4026, 1950, 1256, 1934, 1528, 48, 792, 992, 3786]⟩,
    ⟨#[2729, 328, 4034, 2244, 3764, 3156, 352, 560, 640, 3312, 1556, 3706]⟩]

@[expose] def uCode : Array Code := #[
    ⟨#[3067, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]⟩,
    ⟨#[279, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]⟩,
    ⟨#[3617, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]⟩,
    ⟨#[2103, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]⟩,
    ⟨#[3367, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]⟩,
    ⟨#[3513, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]⟩,
    ⟨#[703, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]⟩,
    ⟨#[3403, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]⟩,
    ⟨#[2779, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]⟩,
    ⟨#[1309, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]⟩,
    ⟨#[997, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]⟩]

@[expose] def kCode : Array Code := #[
    ⟨#[475, 3498, 3838, 1254, 816, 762, 2500, 1626, 1364, 550, 2750, 908]⟩,
    ⟨#[3415, 1898, 300, 1838, 2580, 762, 294, 1050, 1276, 3510, 2768, 1694]⟩,
    ⟨#[3211, 1418, 2490, 2560, 1582, 1616, 1662, 2758, 256, 1086, 1102, 1078]⟩,
    ⟨#[1047, 700, 2190, 3444, 4050, 2378, 1800, 990, 3196, 190, 502, 1180]⟩]


@[expose] def letterCode (ℓ : Int) : Code :=
  if 0 < ℓ then xCode[ℓ.toNat - 1]?.getD 1 else xiCode[(-ℓ).toNat - 1]?.getD 1

@[expose] def codeOfWord (w : List Int) : Code := w.foldl (fun acc ℓ => acc * letterCode ℓ) 1

@[expose] def etaCode (c : Nat) : Code :=
  (List.range 11).foldl (fun acc j => if c.testBit j then acc * (uCode[j]?.getD 1) else acc) 1

@[expose] def pcSeqsT : List (List Nat) :=
  [[0], [0, 1, 0], [0, 0], [0, 0, 1, 0, 0], [0, 2, 0], [3], [3, 1, 3], [2], [2, 1, 2], [1]]

@[expose] def pcSeqT (e : Nat) : List Nat :=
  (List.range 10).flatMap fun j => if e.testBit j then pcSeqsT.getD j [] else []

@[expose] def kelCode (e : Nat) : Code :=
  (pcSeqT e).foldl (fun acc i => acc * (kCode[i]?.getD 1)) 1

@[expose] def codeOfCoord (c e : Nat) : Code := etaCode c * kelCode e

@[expose] def tauInvTab : Array Nat := #[934, 707, 219, 1204, 1234, 1626, 1338, 1491, 1186, 383, 267]

@[expose] def tauInv (t : Nat) : Nat :=
  (List.range 11).foldl (fun acc i => if t.testBit i then acc ^^^ (tauInvTab[i]?.getD 0) else acc) 0

@[noinline, expose] def locCodesOK (L Li : Array (Array V2)) : Bool :=
  (List.range 3).all fun k =>
    compatOK (L[k]?.getD (idRows ())) && rho12 (L[k]?.getD (idRows ())) == xCode[k]?.getD 1 &&
      rho12 (Li[k]?.getD (idRows ())) == xiCode[k]?.getD 1

@[expose] def eFaithOK : Bool :=
  (List.range 2047).all fun c => (etaCode (c + 1)).rows[0]?.getD 0 != 1

@[expose] def etaInEOK : Bool := (List.range 2048).all fun c => (etaCode c).inE

@[expose] def tauOK : Bool :=
  (List.range 2048).all fun t => (etaCode (tauInv t)).rows[0]?.getD 0 == 1 + 2 * t

@[expose] def shapeOK : Bool := xCode.all Code.affShape && xiCode.all Code.affShape

@[expose] def literalsOK : Bool :=
  xCode.all Code.wf && xiCode.all Code.wf && uCode.all Code.wf && kCode.all Code.wf &&
    tauInvTab.all (· < 2048)

@[expose] def affChecks (_ : Unit := ()) : Bool :=
  secOK && locCodesOK (locMats ()) (locInvs ()) && eFaithOK && etaInEOK && tauOK && shapeOK &&
    literalsOK

end CFSG.J4Tree.Native

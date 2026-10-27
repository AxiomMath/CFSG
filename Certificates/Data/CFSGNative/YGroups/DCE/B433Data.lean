module

public import Certificates.Data.CFSGNative.YGroups.DCE.EngineB
public import Certificates.Data.CFSGNative.YGroups.DCE.CertB
public import Certificates.Data.CFSGNative.YGroups.DCE.OmegaBig
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.YGroups.Model432FData

public section

namespace CFSG.YGroups.DCE.B433Native

open CFSG.YGroups.DCE CFSG.YGroups.DCE.B CFSG.Monster.B.Co2.Native

set_option compiler.extract_closed false

@[expose] def deg (_ : Unit := ()) : Nat := 31671

@[expose] def lettersB (_ : Unit) : Array ByteArray :=
  (ModelNative.parsePerms ModelNative.y432FPermText).map (bofArr deg)

@[expose] def wordB (L : Array ByteArray) (w : Array Nat) : ByteArray :=
  w.foldr (fun l acc => bcomp deg L[l]! acc) (bid deg)

@[expose] def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := s
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (s, z ^^^ (z >>> 31))

@[expose] def treeWords (_ : Unit := ()) : Array (Array Nat) := Id.run do
  let mut s : UInt64 := 987654321
  let mut out : Array (Array Nat) := #[]
  for _ in [0:30] do
    let mut w : Array Nat := #[]
    for _ in [0:12] do
      let (s', z) := splitmix s
      s := s'
      w := #[(z % 10).toNat] ++ w
    out := out.push w
  return out

@[expose] def treeGens (L : Array ByteArray) : Array ByteArray :=
  L ++ treeWords.map (wordB L)

@[expose] def x0B : Array Nat := #[
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 15, 16, 18, 20, 22, 23, 25, 28, 29, 31, 32, 36, 39,
    40, 42, 45, 46, 48, 52, 56, 57, 59, 60, 65, 66, 68, 71, 80, 81, 83, 84, 87, 88, 95, 97, 100,
    101, 115, 117, 118, 121, 122, 123, 128, 129, 138, 141, 142, 146, 165, 166, 169, 170, 171, 176,
    177, 179, 180, 188, 201, 202, 206, 207, 214, 239, 240, 241, 246, 247, 248, 250, 251, 259, 260,
    262, 265, 276, 293, 294, 301, 303, 313, 346, 347, 348, 350, 351, 359, 360, 362, 363, 365, 368,
    380, 381, 383, 386, 390, 406, 429, 430, 432, 442, 445, 459, 501, 502, 503, 505, 506, 508, 511,
    523, 524, 526, 529, 530, 532, 535, 539, 620, 622, 625, 640, 641, 645, 713, 714, 716, 717, 719,
    722, 723, 725, 728, 732, 750, 751, 753, 756, 757, 883, 886, 887, 891, 913, 915, 1000, 1001,
    1003, 1006, 1007, 1009, 1012, 1013, 1053, 1057, 1061, 1237, 1238, 1242, 1244, 1278, 1279,
    1378, 1379, 1381, 1384, 1385, 1389, 1393, 1397, 1465, 1712, 1713, 1715, 1721, 1722, 1765,
    1766, 1877, 1881, 1885, 1886, 1902, 1998, 2341, 2343, 2344, 2353, 2354, 2404, 2405, 2524,
    2529, 2535, 2537, 2558, 3152, 3153, 3156, 3157, 3167, 3168, 3215, 3335, 3338, 4131, 4132,
    4133, 4136, 4137, 4143, 4171, 4256, 4257, 5256, 5257, 5259, 5260, 5262, 5265, 5268, 5316,
    6522, 6523, 6524, 6525, 6527, 6529, 6531, 6571, 7999, 8000, 8001, 8002, 8003, 8004, 8005,
    8006, 8022, 9722]

@[expose] def fixB (_ : Unit := ()) : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8]

@[expose] def omegaB433 (L : Array ByteArray) : BigOmega :=
  mkBigOmega deg (treeGens L) x0B 86316516 28

@[expose] def gB (L : Array ByteArray) : ByteArray := wordB L #[1, 2, 5, 0, 8, 9]

@[expose] def relHs (L : Array ByteArray) : Array ByteArray :=
  (List.range 8).foldl (fun acc _ => acc.push (bcomp deg acc.back! (gB L))) #[bid deg]

@[expose] def relPi (L : Array ByteArray) : ByteArray :=
  let gi := binvCand deg (gB L)
  (List.range 9).foldl (fun acc _ => bcomp deg acc gi) (bid deg)

@[expose] def certText (_ : Unit) : String := include_str "../../../../../CFSG/YGroups/Data/b433.cert"

@[expose] def certB433 (_ : Unit) : Cert := parseCert (tokens (certText ()).toUTF8)

@[expose] def nodesOf (O : BigOmega) (L : Array ByteArray) (ws : Array (Nat × Array Nat)) :
    Array (Nat × Nat) :=
  ws.map fun w => (w.1, O.act (wordB L w.2) 0)

@[expose] def ctxB433 (O : BigOmega) (L : Array ByteArray) (cert : Cert) : CtxB where
  n := deg
  letters := L
  cl := 9
  N := O.N
  act := O.act
  actAll := fun σ => O.actAll σ
  nodes := nodesOf O L cert.words
  one := bid deg
  braid := true
  rels := #[(relHs L, relPi L)]

@[expose] def smallOK (O : BigOmega) (L : Array ByteArray) (cert : Cert) : Bool :=
  L.size == 10 && O.N == 86316516 && bisInv deg (gB L) (binvCand deg (gB L)) &&
    allLt cert.words.size fun j => j == 0 || decide (cert.words[j]!.1 < j)

end CFSG.YGroups.DCE.B433Native

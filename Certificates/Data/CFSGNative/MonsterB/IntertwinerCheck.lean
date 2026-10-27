module

public import Certificates.Data.CFSGNative.MonsterB.Max2Pinned
public import Certificates.Data.CFSGNative.MonsterB.BinaryFiles
public import Certificates.Data.CFSGNative.MonsterB.PacketData

public section

namespace CFSG.Monster.B.Bin

set_option compiler.extract_closed false

@[expose] def matOfByteRows (R : Array ByteArray) : Mat := R.map (rowOfBytes 4370 · 0)

@[noinline, expose] def qMats (C : Array (Array ByteArray)) : Array Mat :=
  (Binary.Native.allQRows (Binary.Native.qParts C)).map matOfByteRows

@[expose] def pkRows (k : Nat) : Array (Array (Nat × UInt32)) :=
  (CFSG.Monster.B.Native.packetRows[k]!).map fun row => row.map fun e => (e.1, Dyadic.Native.toU32 e.2)

@[noinline, expose] def binPartsOf (M : Array (Array (Nat × UInt32))) (chunks sz : Nat) :
    Array (Task (Array ByteArray)) :=
  let rows := Dyadic.Native.basisRows
  let pexp := Dyadic.Native.diagExp
  Array.ofFn (n := chunks) fun c => Task.spawn fun _ => Array.ofFn (n := sz) fun j =>
    if c.val * sz + j.val < Dyadic.Native.dim then Dyadic.Native.binRow 3 rows pexp M (c.val * sz + j.val)
    else Dyadic.Native.zeroBytes 552

@[expose] def binRowsOf (M : Array (Array (Nat × UInt32))) (chunks : Nat) : Array ByteArray :=
  Dyadic.Native.assembleRows (binPartsOf M chunks (Dyadic.Native.dim / chunks + 1))
    (Dyadic.Native.dim / chunks + 1)

@[expose] def quotByteRows (C : Array ByteArray) : Array ByteArray :=
  let fr := Binary.Native.bytesOfNat Binary.Native.fixedVector
  Array.ofFn (n := 4370) fun i => Binary.Native.qRowBytes fr (C[Binary.Native.srcIdx i.val]!)

@[noinline, expose] def pkBin (k chunks : Nat) : Mat := matOfByteRows (quotByteRows (binRowsOf (pkRows k) chunks))

@[noinline, expose] def f0Of (Q : Array Mat) (chunks : Nat) : Mat :=
  [pkBin 2 chunks, pkBin 4 chunks, pkBin 5 chunks, pkBin 10 chunks, pkBin 17 chunks].foldl
    (mulP 4370) (mulP 4370 (Q.getD 6 #[]) (Q.getD 0 #[]))

@[expose] def wordMat (Q : Array Mat) (w : List Nat) : Mat :=
  w.foldl (fun X j => mulP 4370 X (Q.getD (j - 1) #[])) (idMat 4370)

@[expose] def probeMat (a b : Mat) : Mat :=
  probeWord.foldl (fun X l => mulP 4370 X (if l then a else b)) (idMat 4370)

@[expose] def rankOK (n : Nat) (M : Mat) (r : Nat) : Bool :=
  let c := rankCert n M
  c.1 == r && mulP n (mulP n c.2.1 M) c.2.2 == diagM n r &&
    mulP n c.2.1 (invM n c.2.1) == idMat n && mulP n c.2.2 (invM n c.2.2) == idMat n

@[expose] def pairChecks (Q : Array Mat) (F0 F BW A B T : Mat) : Bool :=
  let n := 4370
  let I := idMat n
  let q25 := Q.getD 25 #[]
  let ab := mulP n F q25
  let w := probeMat F q25
  Binary.Native.sha256Nat (payload n #[F0]) == f0Sha &&
  Binary.Native.sha256Nat (payload n #[F]) == fSha &&
  mulP n BW F == mulP n F0 BW &&
  mulP n F0 F0 == I && neM n F0 I && rankOK n (addM n F0 I) 2158 &&
  mulP n F T == mulP n T A && mulP n q25 T == mulP n T B &&
  mulP n F F == I && powM n q25 3 == I && neM n q25 I &&
  powM n ab 55 == I && neM n (powM n ab 5) I && neM n (powM n ab 11) I &&
  neM n w I && powM n w 23 == I

@[expose] def pairOK (chunks : Nat) : Bool :=
  let Q := qMats (Binary.Native.allCRows chunks)
  let F0 := f0Of Q chunks
  let BW := wordMat Q conjWord
  let F := mulP 4370 (mulP 4370 (invM 4370 BW) F0) BW
  let Tb := tBytes tLen
  pairChecks Q F0 F BW (seedMat 4370 CFSG.SectionRank.Native.bData.seedA)
    (seedMat 4370 CFSG.SectionRank.Native.bData.seedB) (matOfPayload 4370 Tb 0)

end CFSG.Monster.B.Bin

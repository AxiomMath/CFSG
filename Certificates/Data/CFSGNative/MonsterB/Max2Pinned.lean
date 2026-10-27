module

public import Certificates.Data.CFSGNative.MonsterB.IntertwinerData
public import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.Monster.B.Bin

set_option compiler.extract_closed false

@[noinline, expose] def seedMat (n : Nat) (s : String) : Mat :=
  matOfRows n (CFSG.Sporadic.SmallF2.Native.rowsOfPayload n s)

@[expose] def progStep (n : Nat) (R : Array Mat) (ins : Nat × Nat × Nat) : Array Mat :=
  R.set! ins.2.2 (mulP n (R.getD ins.1 #[]) (R.getD ins.2.1 #[]))

@[expose] def initRegs (n : Nat) (A B : Mat) : Array Mat :=
  #[idMat n, A, B, idMat n, idMat n, idMat n]

@[expose] def runProg (n : Nat) (A B : Mat) : Array Mat := max2Prog.foldl (progStep n) (initRegs n A B)

@[expose] def pinnedChecks (n : Nat) (A B T : Mat) (Tb : ByteArray) : Bool :=
  let I := idMat n
  let R := runProg n A B
  let c := R.getD 1 #[]
  let d := R.getD 2 #[]
  let D := powM n d 24
  let W := mulP n (mulP n (mulP n B B) D) B
  Binary.Native.sha256Nat Tb == tSha &&
  mulP n c c == I && neM n c I &&
  powM n d 48 == I && neM n D I && neM n (powM n d 16) I &&
  mulP n D c == mulP n c D &&
  mulP n T (invM n T) == I &&
  mulP n (mulP n B B) B == I &&
  powM n (mulP n D W) 5 == I

@[expose] def pinnedOK (n : Nat) : Bool :=
  let Tb := tBytes tLen
  pinnedChecks n (seedMat n CFSG.SectionRank.Native.bData.seedA)
    (seedMat n CFSG.SectionRank.Native.bData.seedB) (matOfPayload n Tb 0) Tb

end CFSG.Monster.B.Bin

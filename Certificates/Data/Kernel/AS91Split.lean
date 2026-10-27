module

public import Certificates.Data.Kernel.HJ12KT
public import CFSG.Quasithin.H13.AS91Sec4EightSplitInputs
public import CFSG.Quasithin.H13.AS91Sec4EightInputs
public import CFSG.Quasithin.H13.AS91Sec4SevenInputs

public section

noncomputable section

namespace Certificates.Kernel.AS91Split

open Certificates.Kernel.HJ12K CFSG.KC.Mat12P CFSG.KC.Mat8P CFSG.Quasithin.H13.AS91.Two
  CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour

@[expose] def aQ : ℕ := codeQ aRows48.toList

@[expose] def bQ : ℕ := codeQ bRows48.toList

@[expose] def cQ : ℕ := codeQ cRows48.toList

@[expose] def omQ : ℕ := codeQ omegaRows.toList

@[expose] def sGQ : List ℕ := [aQ, bQ, cQ]

@[expose] def pQ : List ℕ := pRows.map fun r => codeQ r.toList

@[expose] def ebQ : List ℕ := ebRows.map fun r => codeQ r.toList

@[expose] def gamIQ : List ℕ := gamGensI.map fun r => codeQ r.toList

@[expose] def nIQ : List ℕ := nGensI.map fun r => codeQ r.toList

@[expose] def wordP (gs w : List ℕ) : ℕ := (w.map fun i => gs.getD i oneQ).foldr mulQ oneQ

@[expose] def cjP (d : List ℕ × List ℕ × Array ℕ) : List ℕ × List ℕ × ℕ :=
  (d.1, d.2.1, codeQ d.2.2.toList)

@[expose] def conjP (gs : List ℕ) (d : List ℕ × List ℕ × ℕ) (t : ℕ) : Bool :=
  d.1.all (· < gs.length) && d.2.1.all (· < gs.length) &&
    Nat.beq (mulQ (wordP gs d.1) (wordP gs d.2.1)) oneQ &&
    Nat.beq (mulQ (mulQ (wordP gs d.1) d.2.2) (wordP gs d.2.1)) t

@[expose] def sAt (P Eb Sl : List ℕ) : Bool :=
  gensOKQ sGQ && sGQ.all (fun g => P.contains g) && Sl.contains oneQ && closedQ sGQ Sl &&
    (nodupP Sl && Nat.beq Sl.length 16) && Sl.all (fun x => Nat.beq x oneQ || !Eb.contains x)

@[expose] def coreL (P : List ℕ) (s si : ℕ) : List ℕ :=
  P.filter fun r => P.contains (mulQ (mulQ si r) s)

@[expose] def coreAt (s si : ℕ) (C : List ℕ) : Bool :=
  sWord48.all (· < 6) && sWordInv48.all (· < 6) && Nat.beq (mulQ s si) oneQ &&
    Nat.beq (mvNR (unpackQ s) 3) 3 && (nodupP C && Nat.beq C.length 32)

@[expose] def uAt (M : ℕ) : Bool :=
  nodupP uList48 && Nat.beq uList48.length 64 &&
    uList48.all (· < 4096) && uList48.contains 0 &&
    uList48.all (fun x => uList48.all fun y => bitQ M (x ^^^ y)) &&
    uList48.all (fun u => !q0b u) && uList48.all (fun u => bitQ M (mvNR (unpackQ omQ) u)) &&
    sGQ.all (fun g => uList48.all fun u => bitQ M (mvNR (unpackQ g) u)) &&
    uList48.all (fun u => u == 0 || !w1List.contains u)

@[expose] def cjAt (Eb C : List ℕ) : Bool :=
  ebQ.all (fun g => Nat.beq (mulQ g omQ) (mulQ omQ g)) &&
    conjP gamIQ (cjP cjA48) aQ && Eb.contains (cjP cjA48).2.2 &&
    conjP gamIQ (cjP cjB48) bQ && Eb.contains (cjP cjB48).2.2 &&
    conjP gamIQ (cjP cjAB48) (mulQ (mulQ aQ bQ) (mulQ aQ bQ)) && Eb.contains (cjP cjAB48).2.2 &&
    conjP nIQ (cjP cjC48) cQ && C.contains (cjP cjC48).2.2 && !Nat.beq (cjP cjC48).2.2 oneQ &&
    conjP nIQ (cjP cjAC48) (mulQ aQ cQ) && C.contains (cjP cjAC48).2.2 &&
      !Nat.beq (cjP cjAC48).2.2 oneQ &&
    conjP nIQ (cjP cjBC48) (mulQ bQ cQ) && C.contains (cjP cjBC48).2.2 &&
      !Nat.beq (cjP cjBC48).2.2 oneQ &&
    [cQ, mulQ aQ cQ, mulQ bQ cQ].all fun t =>
      Nat.beq (mulQ t t) oneQ && Nat.beq (mulQ (mulQ t omQ) t) (mulQ omQ omQ)

@[expose] def s48Q : ℕ := wordP nIQ sWord48

@[expose] def si48Q : ℕ := wordP nIQ sWordInv48

@[expose] def sQ48 : Bool := sAt (enumQ pQ) (enumQ ebQ) (enumQ sGQ)

@[expose] def coreQ48 : Bool := coreAt s48Q si48Q (coreL (enumQ pQ) s48Q si48Q)

@[expose] def uQ48 : Bool := uAt (Certificates.Kernel.HJ12K.maskOf 0 uList48)

@[expose] def cjQ48 : Bool := cjAt (enumQ ebQ) (coreL (enumQ pQ) s48Q si48Q)

end Certificates.Kernel.AS91Split

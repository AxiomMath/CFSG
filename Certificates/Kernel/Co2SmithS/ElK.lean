module

public import Certificates.Kernel.Co2SmithS.Lets
public import Certificates.Data.Kernel.Co2SmithS.Rows
public import Certificates.Data.Kernel.Co2Smith.Rows
public import CFSG.Certificates.Kernel.Co1F2Sound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2SmithS

open CFSG.KC.Co2InvS CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def mvS (A v : Nat) : Nat := CFSG.KC.M1F2.vmF 22 (CFSG.KC.Co1F2.trK 22 A) v

@[expose] noncomputable def aS : Nat := CFSG.KC.Co2SmithS.wK LT [2]
@[expose] noncomputable def bS : Nat := CFSG.KC.Co2SmithS.wK LT [3]
@[expose] noncomputable def hS (i : Nat) : Nat := CFSG.KC.Co2SmithS.wK LT hWords[i]!
@[expose] noncomputable def zmS : Nat := Nat.xor (LT 0) IDP
@[expose] noncomputable def xS : Nat := CFSG.KC.Co2SmithS.wK LT frameWords[8]!

@[expose] noncomputable def nfS (s v : Nat) : Nat :=
  let m := (List.range 8).foldr (fun i acc => if v.testBit i then mulV (hS i) acc else acc) IDP
  if s == 1 then mulV (LT 0) m else m

@[expose] noncomputable def sigS : List Nat :=
  (List.range 2).flatMap fun s => (List.range 256).map fun v =>
    mvS (nfS s v) wFix * 4194304 + mvS (nfS s v) sepVec

@[expose] def memB (a : Nat) : List Nat → Bool
  | [] => false
  | b :: l => Nat.beq a b || memB a l

@[expose] def nodupB : List Nat → Bool
  | [] => true
  | a :: l => !memB a l && nodupB l

open CFSG.KC.Co2Smith in
@[expose] noncomputable def elemsK : Bool :=
  eqK (powK aS 3) IDP && eqK (powK bS 7) IDP && commK aS (LT 0) && commK bS (LT 0) &&
    Nat.beq (mvS aS wFix) wFix && Nat.beq (mvS bS wFix) wFix && hWords.size == 8 &&
    (List.range 8).all (fun i =>
      eqK (mulV (hS i) (hS i)) IDP && commK (hS i) (LT 0) && eqK (mulV (hS i) zmS) zmS &&
      (List.range 8).all fun j =>
        eqK (mulV (hS i) (hS j))
          (if hypC i j then mulV (mulV (hS j) (hS i)) (LT 0) else mulV (hS j) (hS i))) &&
    (List.range 8).all (fun i => (hWords[i]!).all (· < 4)) &&
    (sigS.length == 512 && nodupB sigS) &&
    (List.range 2).all fun s => (List.range 255).all fun v => !Nat.beq (mvS (nfS s (v + 1)) wFix) wFix

open CFSG.KC.Co2Smith in
@[expose] noncomputable def xFpfK : Bool :=
  frameWords[8]!.all (· < 4) && frameWords.size == 10 &&
    (List.range 2).all fun s => (List.range 255).all fun v => !commK xS (nfS s (v + 1))

theorem elems_ok : elemsK = true := by decide +kernel

theorem xFpf_ok : xFpfK = true := by decide +kernel

theorem subId_ok : subId (CFSG.KC.Co1F2.unpackR 22 (LT 0)) = CFSG.KC.Co1F2.unpackR 22 zmS := by
  decide +kernel

end CertificateChecks.KernelCo2SmithS

end

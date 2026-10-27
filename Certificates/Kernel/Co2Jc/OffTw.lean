module

public import Certificates.Kernel.Co2Jc.OffDefs

public section

namespace CertificateChecks.KernelCo2Jc

open CFSG.Sporadic.Co2Jc.Native

@[expose] noncomputable def mulRowK (s : Nat) : Bool :=
  (List.range 256).all fun i => decide (mulL s i < 256) &&
    Nat.beq (PT (mulL s i)) (CFSG.KC.M1F2.mulF 10 (PT i) (PT s))

@[expose] noncomputable def fixRowK (i : Nat) : Bool :=
  (List.range 1024).all fun m => (FX i).testBit m == Nat.beq (CFSG.KC.M1F2.vmF 10 (PT i) m) m

@[expose] noncomputable def stepLK (l : List Nat) (s : Nat) : List Nat :=
  (List.range 256).filter fun i => l.contains i || (l.map (mulL s)).contains i

@[expose] noncomputable def stepT (l : List Nat) (q : Nat) : Bool :=
  (List.range 256).all fun s =>
    (l.contains s) || Nat.beq s 0 || !(Nat.beq (mulL s s) 0) ||
      !(l.all fun i => Nat.beq (mulL s i) (mulL i s)) ||
      (decide (stI q s < 715) && subs.getD (stI q s) [] == stepLK l s)

@[expose] noncomputable def andM (l : List Nat) : Nat :=
  l.foldl (fun acc i => acc &&& FX i) (2 ^ 1024 - 1)

@[expose] noncomputable def boundT (l : List Nat) : Bool :=
  CFSG.KC.M1F2.strictB (andM l) fun A =>
    decide (l.length * ((List.range 1024).filter fun m => A.testBit m).length ≤ 512)

@[expose] noncomputable def stepC (c : Nat) : Bool :=
  ((subs.zipIdx.drop (32 * c)).take 32).all fun p => stepT p.1 p.2

@[expose] noncomputable def boundC (c : Nat) : Bool :=
  ((subs.drop (32 * c)).take 32).all boundT

end CertificateChecks.KernelCo2Jc

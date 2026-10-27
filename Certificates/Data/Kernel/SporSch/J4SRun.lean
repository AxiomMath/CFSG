module

public import CFSG.Certificates.Kernel.J4Q.RepRank
public import CFSG.Sporadic.GLQ.RegisterProgram

public section

namespace CFSG.KS.SporSch.J4B

open CFSG.KC.J4Q CFSG.KC.Loop CFSG.Sporadic.GLQ

@[expose] noncomputable def stepPK (c rm one : Nat) (regs : List Nat) (ins : Instr) : List Nat :=
  Instr.rec (motive := fun _ => List Nat)
    (fun i j k => strictL (mulJ c rm (getN one regs i) (getN one regs j)) fun a =>
      strictL (mulJ c rm (getN one regs (Nat.add 9 j)) (getN one regs (Nat.add 9 i))) fun b =>
        setN (setN regs k a) (Nat.add 9 k) b)
    (fun i k => strictL (getN one regs (Nat.add 9 i)) fun a => strictL (getN one regs i) fun b =>
      setN (setN regs k a) (Nat.add 9 k) b)
    (fun e i k => strictL (powJ c rm one (getN one regs i) e) fun a =>
      strictL (powJ c rm one (getN one regs (Nat.add 9 i)) e) fun b =>
        setN (setN regs k a) (Nat.add 9 k) b)
    ins

@[expose] noncomputable def runPK (c rm one : Nat) (regs : List Nat) (p : List Instr) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun regs => regs)
    (fun ins _ ih regs => ih (stepPK c rm one regs ins)) p regs

end CFSG.KS.SporSch.J4B

end

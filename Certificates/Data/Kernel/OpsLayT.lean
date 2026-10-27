module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Data.Kernel.OpsMcertT

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.OpsMT

@[expose] noncomputable def getRD (d : Nat) (T : RT) : Nat → Nat :=
  RT.rec (motive := fun _ => Nat → Nat) (fun _ => d)
    (fun _ x _ ihl ihr i => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (ihr (Nat.div (Nat.sub i 1) 2))
        (ihl (Nat.div (Nat.sub i 1) 2)) (Nat.beq (Nat.mod i 2) 1))
      x (Nat.beq i 0)) T

@[expose] noncomputable def stepVG (c : Lay) (g : Nat → Nat) : Op → Nat
  | .mul i j _ => c.mul (g i) (g j)
  | .pow e i _ => powK c (g i) e

@[expose] noncomputable def runCT (c : Lay) (prog : List Op) : RT → (RT → Bool) → Bool :=
  List.rec (motive := fun _ => RT → (RT → Bool) → Bool) (fun T k => k T)
    (fun o _ ih T k => strictB (stepVG c (getRD c.ONE T) o) fun v =>
      setK T (Op.tgt o) v fun T' => ih T' k) prog

@[expose] noncomputable def initRT (c : Lay) (A B n : Nat) : RT := mkT n n (initF A B c.ONE)

@[expose] noncomputable def evalWLG (c : Lay) (g : Nat → Nat) : Word → Nat
  | [] => c.ONE
  | (r, e) :: w => c.mul (powK c (g r) e) (evalWLG c g w)

@[expose] noncomputable def factLG (c : Lay) (g : Nat → Nat) (n : Nat) : MFact → Bool
  | .ord r e => decide (r < n) && decide (0 < e) && decide (e < 65536) &&
      Nat.beq (powK c (g r) e) c.ONE
  | .conj h u w => decide (h < n) && wordOK n u && wordOK n w &&
      Nat.beq (c.mul (g h) (evalWLG c g u)) (c.mul (evalWLG c g w) (g h))
  | .ne w₁ w₂ t => wordOK n w₁ && wordOK n w₂ && decide (t < c.d) &&
      !Nat.beq (c.vec (c.unit t) (evalWLG c g w₁)) (c.vec (c.unit t) (evalWLG c g w₂))
  | .eq w₁ w₂ => wordOK n w₁ && wordOK n w₂ && Nat.beq (evalWLG c g w₁) (evalWLG c g w₂)

@[expose] noncomputable def mcertLT (c : Lay) (A B : Nat) (C : MCert) : Bool :=
  progOK C.nregs C.prog &&
    runCT c C.prog (initRT c A B C.nregs) fun T => C.facts.all (factLG c (getRD c.ONE T) C.nregs)

@[expose] noncomputable def seedsLT (c : Lay) (A B : Nat) (C : MCert) (rA rB : Nat) : Bool :=
  progOK C.nregs C.prog && decide (rA < C.nregs) && decide (rB < C.nregs) &&
    runCT c C.prog (initRT c A B C.nregs) fun T =>
      C.facts.all (factLG c (getRD c.ONE T) C.nregs) &&
      Nat.beq (getRD c.ONE T rA) A && Nat.beq (getRD c.ONE T rB) B

end CFSG.KC.OpsLayK

end

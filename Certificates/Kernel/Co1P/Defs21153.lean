module

public import Certificates.Kernel.Co1P.Defs21152
public import Certificates.Kernel.Co1P.Pin21153

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.Co1F2 CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Patterson.Native

@[expose] def unpack24 (M : Nat) : Array Nat := Array.ofFn (n := 24) fun i => M / 2 ^ (24 * i.val) % 2 ^ 24

@[expose] noncomputable def ord6K (M : Nat) : Nat :=
  (fun p2 => (fun p3 => (fun p4 => (fun p5 => (fun p6 =>
    if eqK M oneK then 1 else if eqK p2 oneK then 2 else if eqK p3 oneK then 3 else
      if eqK p4 oneK then 4 else if eqK p5 oneK then 5 else if eqK p6 oneK then 6 else 0)
    (mulWK p5 M)) (mulWK p4 M)) (mulWK p3 M)) (mulWK p2 M)) (mulWK M M)

@[expose] noncomputable def dclsK (X : Nat) : Nat :=
  if eqK X AL then 0 else if memE X then 1 else
    (fun M => (fun o => if (o == 2 || o == 4 || o == 6) then 2 else if o == 5 then 3 else
      if o == 3 then (if fixDimIs (unpack24 M) 12 then 2 else if fixDimIs (unpack24 M) 8 then 3 else 9)
      else 9) (ord6K M)) (mulWK AL X)

@[expose] noncomputable def atP (k Y : Nat) : Nat := mulWK (mulWK (xeiP k) Y) (xeP k)

@[expose] noncomputable def NT (t r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (tabK 16 NS1 r) (tabK 16 NS0 r) (Nat.beq t 0)

@[expose] noncomputable def PT (t r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (tabK 16 PS1 r) (tabK 16 PS0 r) (Nat.beq t 0)

@[expose] noncomputable def WTt (t m : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (tabK 16 WT1 m) (tabK 16 WT0 m) (Nat.beq t 0)

@[expose] def nT (t : Nat) : Nat := if t == 0 then 10710 else 7950

@[expose] noncomputable def nodesL (t : Nat) : List Nat := (List.range (nT t)).map (NT t)

@[expose] noncomputable def parsL (t : Nat) : List Nat := (List.range (nT t)).map (PT t)

@[expose] noncomputable def witL (t : Nat) : List (Nat × Nat) :=
  (List.range 12600).filterMap fun m => if WTt t m = 0 then none else some (m, WTt t m - 1)

@[expose] noncomputable def MSt (t : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (getL 0 MS1 0) (getL 0 MS0 0) (Nat.beq t 0)

@[expose] noncomputable def RFX (t : Nat) : Nat := repXK (farReps.getD t 0)

@[expose] noncomputable def RFXi (t : Nat) : Nat := repXiK (farReps.getD t 0)

@[expose] noncomputable def treeAtK (t r : Nat) : Bool :=
  (fun n => andB (andB (Nat.blt n 12600) (Nat.beq (dclsK (atP n (RF t))) 2))
    (orB (Nat.beq r 0) (andB (Nat.blt (PT t r) r)
      (adjP (xeP n) (xeiP n) (ptPE (NT t (PT t r))))))) (NT t r)

@[expose] noncomputable def farAtK (t M k : Nat) : Bool :=
  strictB (xeP k) fun X => strictB (xeiP k) fun Xi =>
    andB (orB (Nat.beq (dclsK (mulWK (mulWK Xi (RF t)) X)) 3) (bit M k))
      (strictB (mulWK (mulWK (mulWK (RFX t) X) AL) (mulWK Xi (RFXi t))) fun G =>
        (fun d => orB (orB (Nat.beq d 1) (Nat.beq d 2)) (andB (Nat.beq d 3)
          ((fun w => andB (notB (Nat.beq w 0)) ((fun kk => andB (Nat.blt kk 12600)
            (andB (Nat.beq (dclsK (atP kk (RF t))) 2) (Nat.beq (dclsK (atP kk G)) 2))) (w - 1)))
            (WTt t k)))) (dclsK G))

@[expose] noncomputable def farChunk (t c : Nat) : Bool := strictB (MSt t) fun M => chunkK 12600 (farAtK t M) c

@[expose] noncomputable def tree0Chunk (c : Nat) : Bool := chunkK 10710 (treeAtK 0) c

@[expose] noncomputable def tree1Chunk (c : Nat) : Bool := chunkK 7950 (treeAtK 1) c

@[expose] noncomputable def far0Chunk (c : Nat) : Bool := farChunk 0 c

@[expose] noncomputable def far1Chunk (c : Nat) : Bool := farChunk 1 c

end CertificateChecks.KernelCo1P

end

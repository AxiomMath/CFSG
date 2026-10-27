module

public import Certificates.Kernel.Co1P.Defs21153
public import Certificates.Kernel.Co1P.Pin21154

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.Co1F2 CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Patterson.Native

@[expose] noncomputable def GB (t : Nat) : List Nat := (gensKb.getD t []).map fun j => getL oneK GDS (j - 1)

@[expose] noncomputable def GBI (t : Nat) : List Nat :=
  (gensKb.getD t []).map fun j => getL oneK GDIS (j - 1)

@[expose] noncomputable def RBX (t : Nat) : Nat := repXK (d2Reps.getD t 0)

@[expose] noncomputable def RBXi (t : Nat) : Nat := repXiK (d2Reps.getD t 0)

@[expose] noncomputable def vtxP (p : Nat × Nat) : Nat := mulWK (mulWK p.1 AL) p.2

@[expose] noncomputable def nbP (p : Nat × Nat) (k : Nat) : Nat × Nat :=
  (mulWK p.1 (xeP k), mulWK (xeiP k) p.2)

@[expose] noncomputable def nbG (t m : Nat) : Nat := vtxP (nbP (RBX t, RBXi t) m)

@[expose] noncomputable def pvK (vs : List (Nat × Nat)) (i : Nat) : Nat × Nat := vs.getD (i % 5) (0, 0)

@[expose] noncomputable def pcK : List (Nat × Nat) → PC → Bool
  | vs, .chord r => orB (eqK (vtxP (pvK vs r)) (vtxP (pvK vs (r + 2))))
      (adjP (pvK vs r).1 (pvK vs r).2 (vtxP (pvK vs (r + 2))))
  | vs, .centre r k => andB (Nat.blt k 12600)
      (andB (adjP (nbP (pvK vs r) k).1 (nbP (pvK vs r) k).2 (vtxP (pvK vs (r + 2))))
        (adjP (nbP (pvK vs r) k).1 (nbP (pvK vs r) k).2 (vtxP (pvK vs (r + 3)))))
  | vs, .split r k P => andB (Nat.blt k 12600)
      (andB (adjP (nbP (pvK vs r) k).1 (nbP (pvK vs r) k).2 (vtxP (pvK vs (r + 2))))
        (pcK [pvK vs r, nbP (pvK vs r) k, pvK vs (r + 2), pvK vs (r + 3), pvK vs (r + 4)] P))

@[expose] noncomputable def qcK : Nat × Nat → Nat × Nat → QC → Bool
  | b, g, .pent c c' P => andB (andB (Nat.blt c 12600) (Nat.blt c' 12600))
      (andB (adjP (xeP c) (xeiP c) (vtxP b))
        (andB (adjP g.1 g.2 (vtxP (xeP c', xeiP c')))
          (pcK [(oneK, oneK), (xeP c, xeiP c), b, g, (xeP c', xeiP c')] P)))
  | b, g, .prop k C₁ C₂ => andB (Nat.blt k 12600)
      (andB (adjP (nbP b k).1 (nbP b k).2 (vtxP g)) (andB (qcK b (nbP b k) C₁) (qcK (nbP b k) g C₂)))

@[expose] noncomputable def QMt (t : Nat) : List Nat := [QM0, QM1, QM2, QM3, QM4, QM5, QM6].getD t []

@[expose] noncomputable def OFt (t : Nat) : List Nat := [OF0, OF1, OF2, OF3, OF4, OF5, OF6].getD t []

@[expose] noncomputable def NFt (t : Nat) : List Nat := [NF0, NF1, NF2, NF3, NF4, NF5, NF6].getD t []

@[expose] noncomputable def MQt (t : Nat) : Nat := getL 0 ([MQ0, MQ1, MQ2, MQ3, MQ4, MQ5, MQ6].getD t []) 0

@[expose] noncomputable def MW (t f : Nat) : List Nat :=
  (List.range (getL 0 (NFt t) f)).map fun k => tabK 16 (QMt t) (getL 0 (OFt t) f + k)

@[expose] noncomputable def MWall (t : Nat) : List Nat :=
  (List.range (q2Roots.getD t []).length).flatMap (MW t)

@[expose] noncomputable def recs16 (ms : List Nat) : List (Nat × Nat) := recsK 16 (masksK 16 64 ms)

@[expose] noncomputable def strictL (L : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k List.nil)
    (fun x _ ih k => strictB x fun y => ih fun ys => k (List.cons y ys)) L k

@[expose] noncomputable def q2TreeK (GK GiK : List Nat) (R : Nat) (rs : List (Nat × Nat)) (W : List Nat) :
    Bool :=
  Prod.rec (motive := fun _ => Bool) (fun HS okH => Prod.rec (motive := fun _ => Bool)
    (fun HIS okHi => andB (andB (andB okH okHi) (andB (Nat.beq (lenL GK) 12) (invsOK GK GiK)))
      (strictL (conjL R HS HIS) fun P => andB (distinctK 13 (modL P)) (eqLK P W)))
    (treePts (hisAct GiK) 12 oneK rs)) (treePts (hsAct GK) 12 oneK rs)

@[expose] noncomputable def q2Tree (t f : Nat) : Bool :=
  q2TreeK (GB t) (GBI t) (nbG t ((q2Roots.getD t []).getD f 0))
    (recs16 ((q2Masks.getD t []).getD f [])) ((MW t f).map (nbG t))

@[expose] noncomputable def q2SmallK (t : Nat) : Bool :=
  andB (andB (andB ((GB t).all fun g => andB (eqK (mulWK g AL) (mulWK AL g))
      (eqK (mulWK g (RB t)) (mulWK (RB t) g)))
    (andB (Nat.beq (q2Roots.getD t []).length (q2Certs.getD t []).length)
      (Nat.beq (q2Roots.getD t []).length (q2Masks.getD t []).length)))
    (Nat.beq (bitsOf (MWall t)) (MQt t)))
    (((q2Roots.getD t []).zip (q2Certs.getD t [])).all fun p =>
      andB (Nat.blt p.1 12600) (qcK (RBX t, RBXi t) (nbP (RBX t, RBXi t) p.1) p.2))

@[expose] noncomputable def q2AtK (t M m : Nat) : Bool :=
  orB (bit M m) ((fun d => orB (Nat.beq d 1) (Nat.beq d 3)) (dclsK (nbG t m)))

@[expose] noncomputable def q2Chunk (t c : Nat) : Bool := strictB (MQt t) fun M => chunkK 12600 (q2AtK t M) c

@[expose] noncomputable def q2T0 (f : Nat) : Bool := q2Tree 0 f
@[expose] noncomputable def q2T1 (f : Nat) : Bool := q2Tree 1 f
@[expose] noncomputable def q2T2 (f : Nat) : Bool := q2Tree 2 f
@[expose] noncomputable def q2T3 (f : Nat) : Bool := q2Tree 3 f
@[expose] noncomputable def q2T4 (f : Nat) : Bool := q2Tree 4 f
@[expose] noncomputable def q2T5 (f : Nat) : Bool := q2Tree 5 f
@[expose] noncomputable def q2T6 (f : Nat) : Bool := q2Tree 6 f

@[expose] noncomputable def q2L0 (c : Nat) : Bool := q2Chunk 0 c
@[expose] noncomputable def q2L1 (c : Nat) : Bool := q2Chunk 1 c
@[expose] noncomputable def q2L2 (c : Nat) : Bool := q2Chunk 2 c
@[expose] noncomputable def q2L3 (c : Nat) : Bool := q2Chunk 3 c
@[expose] noncomputable def q2L4 (c : Nat) : Bool := q2Chunk 4 c
@[expose] noncomputable def q2L5 (c : Nat) : Bool := q2Chunk 5 c
@[expose] noncomputable def q2L6 (c : Nat) : Bool := q2Chunk 6 c

end CertificateChecks.KernelCo1P

end

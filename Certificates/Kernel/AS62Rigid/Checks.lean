module

public import Certificates.Kernel.AS62Rigid.Data
public import Certificates.Data.Kernel.AS62RigidK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAS62

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.AS62 CFSG.LargeExtraspecial.AS62
  CFSG.LargeExtraspecial.AS62.Rigid CFSG.LargeExtraspecial.AS62.Sem CFSG.Quasithin.H13.F431.U42Aut

@[expose] noncomputable def allK (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(f i, ih)) n

@[expose] noncomputable def anyK (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => bIf(f i, true, ih)) n

@[expose] noncomputable def YP (j : Nat) : Nat :=
  nIf(Nat.beq j 0, PID, nIf(Nat.beq j 1, GK 4, pc (GK 4) (GK 4)))

@[expose] noncomputable def YPI (j : Nat) : Nat :=
  nIf(Nat.beq j 0, PID, nIf(Nat.beq j 1, GKI 4, pc (GKI 4) (GKI 4)))

@[expose] noncomputable def P1E (i : Nat) : Nat := pc (YP (Nat.div i 192)) (BK (Nat.mod i 192))

@[expose] noncomputable def P1I (i : Nat) : Nat := pc (BKI (Nat.mod i 192)) (YPI (Nat.div i 192))

@[expose] noncomputable def BHE (f : Nat) : Nat := nIf(Nat.blt f 192, BK f, pc (BK (Nat.sub f 192)) FH)

@[expose] noncomputable def BHI (f : Nat) : Nat :=
  nIf(Nat.blt f 192, BKI f, pc FH (BKI (Nat.sub f 192)))

@[expose] noncomputable def rB (E EI : Nat → Nat) (k : Nat) : Bool := relK E EI (relsB.getD k [])

@[expose] noncomputable def r1E (E EI : Nat → Nat) (k : Nat) : Bool :=
  relK E EI (rels1Extra.getD k [])

@[expose] noncomputable def r2E (E EI : Nat → Nat) (k : Nat) : Bool :=
  relK E EI (rels2Extra.getD k [])

@[expose] noncomputable def u0K (a : Nat) : Bool :=
  bAnd(rB (tup5 (BK a) PID PID PID PID) (tup5 (BKI a) PID PID PID PID) 0,
    bIf(Nat.beq (BK a) PID, false, true))
@[expose] noncomputable def u1K (b : Nat) : Bool :=
  rB (tup5 PID (BK b) PID PID PID) (tup5 PID (BKI b) PID PID PID) 1
@[expose] noncomputable def u2K (c : Nat) : Bool :=
  rB (tup5 PID PID (BK c) PID PID) (tup5 PID PID (BKI c) PID PID) 2
@[expose] noncomputable def u3K (d : Nat) : Bool :=
  rB (tup5 PID PID PID (BK d) PID) (tup5 PID PID PID (BKI d) PID) 3
@[expose] noncomputable def uyK (u : Nat) : Bool :=
  r1E (tup5 PID PID PID PID (P1E u)) (tup5 PID PID PID PID (P1I u)) 0
@[expose] noncomputable def usK (v : Nat) : Bool :=
  r2E (tup5 PID PID PID PID (P2K v)) (tup5 PID PID PID PID (P2KI v)) 0
@[expose] noncomputable def p5K (a b : Nat) : Bool :=
  rB (tup5 (BK a) (BK b) PID PID PID) (tup5 (BKI a) (BKI b) PID PID PID) 5
@[expose] noncomputable def p6K (a c : Nat) : Bool :=
  rB (tup5 (BK a) PID (BK c) PID PID) (tup5 (BKI a) PID (BKI c) PID PID) 6
@[expose] noncomputable def p9K (b c : Nat) : Bool :=
  rB (tup5 PID (BK b) (BK c) PID PID) (tup5 PID (BKI b) (BKI c) PID PID) 9
@[expose] noncomputable def p4K (c d : Nat) : Bool :=
  rB (tup5 PID PID (BK c) (BK d) PID) (tup5 PID PID (BKI c) (BKI d) PID) 4
@[expose] noncomputable def p7K (a d : Nat) : Bool :=
  rB (tup5 (BK a) PID PID (BK d) PID) (tup5 (BKI a) PID PID (BKI d) PID) 7
@[expose] noncomputable def p8K (b d : Nat) : Bool :=
  rB (tup5 PID (BK b) PID (BK d) PID) (tup5 PID (BKI b) PID (BKI d) PID) 8
@[expose] noncomputable def q1K (d u : Nat) : Bool :=
  r1E (tup5 PID PID PID (BK d) (P1E u)) (tup5 PID PID PID (BKI d) (P1I u)) 1
@[expose] noncomputable def q2K (b u : Nat) : Bool :=
  r1E (tup5 PID (BK b) PID PID (P1E u)) (tup5 PID (BKI b) PID PID (P1I u)) 2
@[expose] noncomputable def s1K (d v : Nat) : Bool :=
  r2E (tup5 PID PID PID (BK d) (P2K v)) (tup5 PID PID PID (BKI d) (P2KI v)) 1
@[expose] noncomputable def s2K (c v : Nat) : Bool :=
  r2E (tup5 PID PID (BK c) PID (P2K v)) (tup5 PID PID (BKI c) PID (P2KI v)) 2
@[expose] noncomputable def r10K (a b c d : Nat) : Bool :=
  rB (tup5 (BK a) (BK b) (BK c) (BK d) PID) (tup5 (BKI a) (BKI b) (BKI c) (BKI d) PID) 10
@[expose] noncomputable def ry3K (a b c u : Nat) : Bool :=
  r1E (tup5 (BK a) (BK b) (BK c) PID (P1E u)) (tup5 (BKI a) (BKI b) (BKI c) PID (P1I u)) 3
@[expose] noncomputable def rs3K (c d v : Nat) : Bool :=
  r2E (tup5 PID PID (BK c) (BK d) (P2K v)) (tup5 PID PID (BKI c) (BKI d) (P2KI v)) 3
@[expose] noncomputable def rs4K (a b v : Nat) : Bool :=
  r2E (tup5 (BK a) (BK b) PID PID (P2K v)) (tup5 (BKI a) (BKI b) PID PID (P2KI v)) 4

@[expose] noncomputable def cj (f g : Nat) : Nat := pc (pc (BHE f) g) (BHI f)

@[expose] noncomputable def conjK (f a b c d u v : Nat) : Bool :=
  bAnd(Nat.beq (cj f (GK 0)) (BK a), bAnd(Nat.beq (cj f (GK 1)) (BK b),
    bAnd(Nat.beq (cj f (GK 2)) (BK c), bAnd(Nat.beq (cj f (GK 3)) (BK d),
    bAnd(Nat.beq (cj f (GK 4)) (P1E u), Nat.beq (cj f (GK 5)) (P2K v))))))

@[expose] noncomputable def AL : List Nat := (List.range 192).filter (bitK (UN 0))
@[expose] noncomputable def T2L : List Nat := (List.range 192).filter (bitK (UN 1))
@[expose] noncomputable def E2L : List Nat := (List.range 192).filter (bitK (UN 2))
@[expose] noncomputable def D3L : List Nat := (List.range 192).filter (bitK (UN 3))
@[expose] noncomputable def U3L : List Nat := (List.range 576).filter (bitK (UN 4))
@[expose] noncomputable def V2L : List Nat := (List.range 960).filter (bitK (UN 5))

@[expose] noncomputable def ckGB : Bool :=
  allK 6 fun k => bAnd(Nat.beq (uLists.getD k []).length 45, bAnd(Nat.beq (uInvLists.getD k []).length 45,
    allK 45 fun i => bAnd(Nat.beq ((uLists.getD k []).getD i 0) (pg 6 (mask 6) (GK k) i),
      Nat.beq ((uInvLists.getD k []).getD i 0) (pg 6 (mask 6) (GKI k) i))))

@[expose] noncomputable def ckFHB : Bool :=
  bAnd(Nat.beq fhatL.length 45, allK 45 fun i => Nat.beq (fhatL.getD i 0) (pg 6 (mask 6) FH i))

@[expose] noncomputable def ckBWB : Bool :=
  (List.finRange 192).all fun k => bAnd(Nat.beq (codeW GK GKI (fun i => i.val) (bWord k)) (BK k.val),
    Nat.beq (codeW GK GKI (fun i => i.val) (invWord (bWord k))) (BKI k.val))

@[expose] noncomputable def ckP2WB : Bool :=
  (List.finRange 960).all fun k => bAnd(Nat.beq (codeW GK GKI code2 (h2Word k)) (P2K k.val),
    Nat.beq (codeW GK GKI code2 (invWord (h2Word k))) (P2KI k.val))

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 45 6 (mask 6) (45 * 6) p

@[expose] noncomputable def ckCanonB : Bool :=
  bAnd(cn PID, bAnd(cn FH, bAnd(allK 6 (fun k => bAnd(cn (GK k), cn (GKI k))),
    bAnd(allK 192 (fun k => bAnd(cn (BK k), cn (BKI k))),
      allK 960 (fun k => bAnd(cn (P2K k), cn (P2KI k)))))))

theorem ckG : ckGB = true := by quickRfl
theorem ckFH : ckFHB = true := by quickRfl
theorem ckBW : ckBWB = true := by quickRfl
theorem ckP2W : ckP2WB = true := by quickRfl
theorem ckCanon : ckCanonB = true := by quickRfl

theorem ckU : allK 192 (fun i => bAnd(beqB (bitK (UN 0) i) (u0K i),
    bAnd(beqB (bitK (UN 1) i) (u1K i), bAnd(beqB (bitK (UN 2) i) (u2K i),
      beqB (bitK (UN 3) i) (u3K i))))) = true := by quickRfl
theorem ckUY : allK 576 (fun i => beqB (bitK (UN 4) i) (uyK i)) = true := by quickRfl
theorem ckUS : allK 960 (fun i => beqB (bitK (UN 5) i) (usK i)) = true := by quickRfl

theorem ckP5 : AL.all (fun a => T2L.all fun b => beqB (bitK (P5 a) b) (p5K a b)) = true := by
  quickRfl
theorem ckP6 : AL.all (fun a => E2L.all fun c => beqB (bitK (P6 a) c) (p6K a c)) = true := by
  quickRfl
theorem ckP9 : T2L.all (fun b => E2L.all fun c => beqB (bitK (P9 b) c) (p9K b c)) = true := by
  quickRfl
theorem ckP4 : E2L.all (fun c => D3L.all fun d => beqB (bitK (P4 c) d) (p4K c d)) = true := by
  quickRfl
theorem ckP7 : AL.all (fun a => D3L.all fun d => beqB (bitK (P7 a) d) (p7K a d)) = true := by
  quickRfl
theorem ckP8 : T2L.all (fun b => D3L.all fun d => beqB (bitK (P8 b) d) (p8K b d)) = true := by
  quickRfl
theorem ckQ1 : D3L.all (fun d => U3L.all fun u => beqB (bitK (Q1 d) u) (q1K d u)) = true := by
  quickRfl
theorem ckQ2 : T2L.all (fun b => U3L.all fun u => beqB (bitK (Q2 b) u) (q2K b u)) = true := by
  quickRfl
theorem ckR1 : D3L.all (fun d => V2L.all fun v => beqB (bitK (R1 d) v) (s1K d v)) = true := by
  quickRfl
theorem ckR2 : E2L.all (fun c => V2L.all fun v => beqB (bitK (R2 c) v) (s2K c v)) = true := by
  quickRfl
@[expose] noncomputable def rigidKB : Bool :=
  AL.all fun a => T2L.all fun b => bIf(bitK (P5 a) b,
    E2L.all fun c => bIf(bAnd(bitK (P6 a) c, bitK (P9 b) c),
      D3L.all fun d => bIf(bAnd(bitK (P4 c) d, bAnd(bitK (P7 a) d,
          bAnd(bitK (P8 b) d, r10K a b c d))),
        U3L.all fun u => bIf(bAnd(bitK (Q1 d) u, bAnd(bitK (Q2 b) u, ry3K a b c u)),
          V2L.all fun v => bIf(bAnd(bitK (R1 d) v, bAnd(bitK (R2 c) v,
              bAnd(rs3K c d v, rs4K a b v))),
            anyK 384 (fun f => bAnd(bitK (C0 a) f, bAnd(bitK (C1 b) f, conjK f a b c d u v))),
            true),
          true),
        true),
      true),
    true)

theorem rigidK : rigidKB = true := by quickRfl

theorem ckDistinct : bAnd(nodupK ((List.range 192).map BK), bAnd(nodupK ((List.range 576).map P1E),
    nodupK ((List.range 960).map P2K))) = true := by quickRfl

end CertificateChecks.KernelAS62

end

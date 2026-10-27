module

public import Certificates.Data.Kernel.MonsterPcFive.E3

public section

namespace CFSG.KC.MonPcFive

@[expose] def aR0 : RV := ⟨1, 0, 0, 0, 1, 1, 0⟩

@[expose] def aR1 : RV := ⟨0, 1, 0, 3, 2, 3, 0⟩

@[expose] def aR2 : RV := ⟨0, 0, 1, 4, 1, 3, 0⟩

@[expose] def aR (k : Nat) : RV :=
  bif k.beq 0 then aR0 else bif k.beq 1 then aR1 else bif k.beq 2 then aR2 else RV.xg

@[expose] def d4 (n i : Nat) : Nat :=
  bif i.beq 0 then n / 125 % 5 else bif i.beq 1 then n / 25 % 5 else bif i.beq 2 then n / 5 % 5
  else n % 5

@[expose] def iotaR (n : Nat) : RV :=
  mulR cmM (mulR cmM (mulR cmM (powR cmM aR0 (n / 125 % 5)) (powR cmM aR1 (n / 25 % 5)))
    (powR cmM aR2 (n / 5 % 5))) (RV.xc (n % 5))

@[expose] def iotaV (n : Nat) : V9 := ⟨0, 0, iotaR n⟩

@[expose] def genV (i : Nat) : V9 := dec (5 ^ (8 - i))

@[expose] def aOK (nrm : List Nat) : Bool :=
  (mulR cmM aR0 aR1).beq (mulR cmM aR1 aR0) && (mulR cmM aR0 aR2).beq (mulR cmM aR2 aR0) &&
    (mulR cmM aR1 aR2).beq (mulR cmM aR2 aR1) && (powR cmM aR0 5).beq RV.one &&
    (powR cmM aR1 5).beq RV.one && (powR cmM aR2 5).beq RV.one &&
    allBelow (fun i => allBelow (fun k =>
      (mulV (genV i) ⟨0, 0, aR k⟩).beq (mulV (iotaV (nthN nrm (4 * i + k))) (genV i))) 4) 9

@[expose] def cosT (k : Nat) : V9 :=
  ⟨k / 625 % 5, k / 125 % 5, ⟨0, 0, 0, k / 25 % 5, k / 5 % 5, k % 5, 0⟩⟩

@[expose] def cosOK (rcs : List Nat) (k d : Nat) : Bool :=
  (mulV (dec (d / 153125)) (cosT k)).beq
    (mulV (mulV (cosT (nthN rcs (d / 625 % 245))) (iotaV (d % 625))) (dec (d / 153125)))

@[expose] def cosRun (rcs : List Nat) : Nat → List Nat → Bool
  | _, [] => true
  | k, d :: ds => cosOK rcs k d && cosRun rcs (k + 1) ds

@[expose] def sel4 (c0 c1 c2 c3 j : Nat) : Nat :=
  bif j.beq 0 then c0 else bif j.beq 1 then c1 else bif j.beq 2 then c2 else c3

@[expose] def colOK (t : V9) (c0 c1 c2 c3 : Nat) : Bool :=
  allBelow (fun j => (mulV ⟨0, 0, aR j⟩ t).beq (mulV t (iotaV (sel4 c0 c1 c2 c3 j)))) 4

@[expose] def delta (i j : Nat) : Nat := bif i.beq j then 1 else 0

@[expose] def piE (c0 c1 c2 c3 s0 s1 s2 s3 i j : Nat) : Nat :=
  (delta i j + (delta i 0 + 4 * d4 c0 i) * d4 (sel4 s0 s1 s2 s3 j) 0 +
    (delta i 1 + 4 * d4 c1 i) * d4 (sel4 s0 s1 s2 s3 j) 1 +
    (delta i 2 + 4 * d4 c2 i) * d4 (sel4 s0 s1 s2 s3 j) 2 +
    (delta i 3 + 4 * d4 c3 i) * d4 (sel4 s0 s1 s2 s3 j) 3) % 5

@[expose] def inJ (m i : Nat) : Bool := (m / 2 ^ i % 2).beq 1

@[expose] def piOK (c0 c1 c2 c3 s0 s1 s2 s3 m : Nat) : Bool :=
  allBelow (fun i => inJ m i || allBelow (fun j => (piE c0 c1 c2 c3 s0 s1 s2 s3 i j).beq 0) 4) 4

@[expose] def ptVec (m j : Nat) : Nat :=
  let c3 := bif inJ m 3 then j % 5 else 0
  let q2 := bif inJ m 3 then j / 5 else j
  let c2 := bif inJ m 2 then q2 % 5 else 0
  let q1 := bif inJ m 2 then q2 / 5 else q2
  let c1 := bif inJ m 1 then q1 % 5 else 0
  let q0 := bif inJ m 1 then q1 / 5 else q1
  let c0 := bif inJ m 0 then q0 % 5 else 0
  125 * c0 + 25 * c1 + 5 * c2 + c3

@[expose] def ptCnt (m : Nat) : Nat :=
  (bif inJ m 0 then 5 else 1) * (bif inJ m 1 then 5 else 1) * (bif inJ m 2 then 5 else 1) *
    (bif inJ m 3 then 5 else 1)

@[expose] def ptOK (rep : List Nat) (nc : Nat) (t : V9) (c d : Nat) : Bool :=
  let e := mulV t (iotaV c)
  bif d.beq 0 then e.isOne || !(ord5 e)
  else Nat.ble 1 (d % 1024) && Nat.blt (d % 1024 - 1) nc &&
    (mulV (dec (d / 1024)) e).beq (mulV (dec (nthN rep (d % 1024 - 1))) (dec (d / 1024)))

@[expose] def ptsRun (rep : List Nat) (nc : Nat) (t : V9) (m : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | j, d :: ds => ptOK rep nc t (ptVec m j) d && ptsRun rep nc t m (j + 1) ds

@[expose] def repsRun (rcs rep : List Nat) (nc : Nat) :
    Nat → Nat → List Nat → List Nat → Bool
  | _, 0, _, _ => true
  | r, n + 1, c0 :: c1 :: c2 :: c3 :: s0 :: s1 :: s2 :: s3 :: m :: hs, ps =>
    let t := cosT (nthN rcs r)
    colOK t c0 c1 c2 c3 && piOK c0 c1 c2 c3 s0 s1 s2 s3 m &&
      (ps.take (ptCnt m)).length.beq (ptCnt m) && ptsRun rep nc t m 0 (ps.take (ptCnt m)) &&
      repsRun rcs rep nc (r + 1) n hs (ps.drop (ptCnt m))
  | _, _ + 1, _, _ => false

@[expose] def memK (n : Nat) : List Nat → Bool
  | [] => false
  | a :: l => n.beq a || memK n l

@[expose] def autW (j : Nat) : List Nat :=
  bif j.beq 0 then [1681607, 146854, 17671, 9050, 7522, 6053, 5036, 10615, 1]
  else bif j.beq 1 then [1033832, 296282, 2990, 67983, 16197, 30666, 15153, 76250, 2]
  else [1343804, 1877722, 54584, 50432, 66724, 56293, 38455, 22670, 3]

@[expose] def alphaW (ws : List Nat) (v : V9) : V9 :=
  mulV (mulV (mulV (mulV (mulV (mulV (mulV (mulV (powV (dec (nthN ws 0)) v.e0)
    (powV (dec (nthN ws 1)) v.e1)) (powV (dec (nthN ws 2)) v.r.a0))
    (powV (dec (nthN ws 3)) v.r.a1)) (powV (dec (nthN ws 4)) v.r.a2))
    (powV (dec (nthN ws 5)) v.r.a3)) (powV (dec (nthN ws 6)) v.r.a4))
    (powV (dec (nthN ws 7)) v.r.a5)) (powV (dec (nthN ws 8)) v.r.c)

@[expose] def stepW (rep depth : List Nat) (nc c c' w : Nat) (v' : V9) : Bool :=
  Nat.blt c' nc && Nat.blt (nthN depth c') (nthN depth c) &&
    (mulV (dec w) v').beq (mulV (dec (nthN rep c')) (dec w))

@[expose] def classW (rep depth kind arg cls wit : List Nat) (nc c : Nat) : Bool :=
  let r := dec (nthN rep c)
  let k := nthN kind c
  let a := nthN arg c
  bif k.beq 0 then memK (nthN rep c) repK
  else bif k.beq 1 then Nat.blt a 3 && stepW rep depth nc c (nthN cls c) (nthN wit c) (alphaW (autW a) r)
  else Nat.ble 2 a && Nat.blt a 5 && ord5 r && stepW rep depth nc c (nthN cls c) (nthN wit c) (powV r a)

@[expose] def fusW (rep depth kind arg cls wit : List Nat) (nc lo n : Nat) : Bool :=
  allBelow (fun c => classW rep depth kind arg cls wit nc (lo + c)) n

end CFSG.KC.MonPcFive

end

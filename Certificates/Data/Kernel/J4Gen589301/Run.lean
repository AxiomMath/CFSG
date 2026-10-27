module

public import Certificates.Data.Kernel.J4Q.Mat
public import Certificates.Data.J4M4GenData

public section

namespace CFSG.KC.J4Gen

open CFSG.KC.Loop CFSG.KC.J4Q CFSG.Quasithin.KGC31.J4M4.Gen

@[expose] noncomputable def rdK (one : Nat) (mem : List Nat) (n i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) one (getN one mem (Nat.sub (Nat.sub n (nat_lit 1)) i))
    (Nat.blt i n)

@[expose] noncomputable def runK (c rm one pad : Nat) (inp : List Nat) (fin : List Nat → Nat → Bool) :
    List Line → List Nat → Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → List Nat → Bool)
    (fun mem n _ => fin mem n)
    (fun l _ ih mem n invs =>
      Line.rec (motive := fun _ => Bool)
        (fun k => strictB (getN one inp k) fun v => ih (v :: mem) (Nat.succ n) invs)
        (fun i j => strictB (rdK one mem n i) fun x => strictB (rdK one mem n j) fun y =>
          strictB (mulJ c rm x y) fun v => ih (v :: mem) (Nat.succ n) invs)
        (fun i => strictB (rdK one mem n i) fun x =>
          List.rec (motive := fun _ => Bool) false
            (fun h hs _ => andB (canonJ pad h) (andB (Nat.beq (mulJ c rm x h) one)
              (ih (h :: mem) (Nat.succ n) hs))) invs)
        (fun i e => strictB (rdK one mem n i) fun x =>
          strictB (powJ c rm one x e) fun v => ih (v :: mem) (Nat.succ n) invs)
        l)

@[expose] noncomputable def factsK (c rm one pad Z C U F AP BP A B G GI : Nat) : Bool :=
  andB (Nat.beq (mulJ c rm Z Z) one) (andB (Nat.beq (powJ c rm one C (nat_lit 11)) one)
  (andB (Nat.beq (mulJ c rm C Z) (mulJ c rm Z C)) (andB (Nat.beq (mulJ c rm U Z) (mulJ c rm F U))
  (andB (Nat.beq (mulJ c rm AP G) (mulJ c rm G A)) (andB (Nat.beq (mulJ c rm BP G) (mulJ c rm G B))
  (andB (canonJ pad G) (andB (canonJ pad GI) (andB (Nat.beq (mulJ c rm G GI) one)
    (Nat.beq (mulJ c rm GI G) one)))))))))

@[expose] def parseL (L : List Char) : List Line :=
  ((L.splitOnP Char.isWhitespace).filter fun t => !t.isEmpty).map Line.ofToken

end CFSG.KC.J4Gen

end

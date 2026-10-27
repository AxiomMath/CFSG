module

public import Certificates.Data.Kernel.J4Q.QT2A
public import Certificates.Data.Kernel.LocalQT.Core

public section

namespace CFSG.KC.J4Q

open CFSG.KC.Loop CFSG.KC.LQT.Syl

@[expose] noncomputable def dropK (n : Nat) (l : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) l
    (fun _ ih => List.rec (motive := fun _ => List Nat) List.nil (fun _ t _ => t) ih) n

@[expose] noncomputable def headK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ _ => x) l

@[expose] noncomputable def vptsK (rm root : Nat) (EN : List Nat) : List Nat :=
  List.cons root (List.map (fun e => Nat.land e rm) EN)

@[expose] noncomputable def vecLFrom (x : Nat) (rs : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun r _ ih k acc => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ k) acc)
      (strictN (Nat.xor acc r) (ih (Nat.succ k)))
      (Nat.beq (Nat.land (Nat.shiftRight x k) (nat_lit 1)) (nat_lit 1))) rs

@[expose] noncomputable def vecLJ (x : Nat) (rs : List Nat) : Nat := vecLFrom x rs (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def rowsOfJ (rm M : Nat) : List Nat :=
  List.map (fun k => rowJ rm M k) (Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun k ih acc => ih (List.cons k acc)) (nat_lit 112) List.nil)

@[expose] noncomputable def vtGo (rm : Nat) (Rs : List (List Nat)) (EN : List Nat) :
    List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Nat → Bool) (fun _ _ _ => true)
    (fun e _ ih cur ci k =>
      (fun par lab v => andB (Nat.ble ci par) (andB (Nat.blt par k)
        (andB (Nat.blt lab (List.length Rs))
          ((fun cur' => andB (Nat.beq (vecLJ (headK cur') (List.getD Rs lab List.nil)) v)
            (ih cur' par (Nat.succ k))) (dropK (Nat.sub par ci) cur)))))
        (Nat.shiftRight e (nat_lit 114)) (Nat.land (Nat.shiftRight e (nat_lit 112)) (nat_lit 3))
        (Nat.land e rm))
    EN

@[expose] noncomputable def vtreeK (rm : Nat) (Rs : List (List Nat)) (root : Nat) (EN : List Nat) : Bool :=
  vtGo rm Rs EN (vptsK rm root EN) (nat_lit 0) (nat_lit 1)

@[expose] noncomputable def sincK (l : List Nat) (b : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih b => andB (Nat.blt b x) (ih x)) l b

@[expose] noncomputable def imgsK (Rs : List (List Nat)) (P : List Nat) : List Nat :=
  List.flatten (List.map (fun x => List.map (fun rs => vecLJ x rs) Rs) P)

@[expose] noncomputable def vtChunkK (rm : Nat) (Rs : List (List Nat)) (P ch : List Nat) (p₀ k₀ : Nat) :
    Bool :=
  vtGo rm Rs ch (dropK p₀ P) p₀ k₀

@[expose] noncomputable def inSK (pc SP : List Nat) : Bool := eqLK (diffS (sortN pc) SP) List.nil

@[expose] noncomputable def spInK (sc : List Nat) (Pch : List (List Nat)) : Bool :=
  eqLK (List.foldl (fun acc pc => diffS acc (sortN pc)) sc Pch) List.nil

@[expose] noncomputable def clK (Rs : List (List Nat)) (pc SP : List Nat) : Bool :=
  eqLK (diffS (dedupS (sortN (imgsK Rs pc))) SP) List.nil

end CFSG.KC.J4Q

end

module

public import Certificates.Data.Kernel.SporLatDcCode

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def omOKGnd {Lab : Type} [DecidableEq Lab] [Inhabited Lab] (actF : Nat → Lab → Lab)
    (x0 : Lab) (nl : Nat) (O : OmegaData Lab) : Bool :=
  decide (O.lbl[0]! = x0) && decide (0 < O.lbl.size) &&
    (List.range nl).all (fun l => (List.range O.lbl.size).all fun i =>
      decide ((O.pn[l]!)[i]! < O.lbl.size) &&
        decide (O.lbl[(O.pn[l]!)[i]!]! = actF l O.lbl[i]!)) &&
    (List.range O.lbl.size).all (fun i => i == 0 ||
      (decide (O.par[i]! < i) && decide (O.via[i]! < nl) && (O.pn[O.via[i]!]!)[O.par[i]!]! == i))

@[expose] def ordOK (O : OmegaData (List Nat)) (ord : List Nat) : Bool :=
  Nat.beq ord.length O.lbl.size && ord.all (fun i => Nat.blt i O.lbl.size) &&
    sortedLt (ord.map fun i => O.lbl[i]!)

@[expose] def omCodeOKS (n : Nat) (ts : Array (Array Nat)) (x0 : List Nat)
    (O : OmegaData (List Nat)) (ord : List Nat) : Bool :=
  omOKGnd (fun l x => codeSetT n (ts.getD l #[]) x) x0 ts.size O && ordOK O ord

@[expose] def lookC (B : Nat) (C : List (List (List Nat))) (k : Nat) : List Nat :=
  (C.getD (Nat.div k B) []).getD (Nat.mod k B) []

@[expose] def chunksOK (B : Nat) : List (List (List Nat)) → Bool
  | [] => false
  | [c] => Nat.blt 0 c.length && Nat.ble c.length B
  | c :: d :: l => Nat.beq c.length B && chunksOK B (d :: l)

@[expose] def omC (actF : Nat → List Nat → List Nat) (x0 : List Nat) (nl B : Nat)
    (C : List (List (List Nat))) (rows : List (List Nat)) (par via ord : List Nat) : Bool :=
  chunksOK B C && (C.flatten.headD [] == x0) &&
    Nat.beq rows.length nl &&
    allIdx (fun l row => Nat.beq row.length C.flatten.length &&
      (List.zip row C.flatten).all fun e =>
        Nat.blt e.1 C.flatten.length && lookC B C e.1 == actF l e.2) 0 rows &&
    Nat.beq par.length C.flatten.length && Nat.beq via.length C.flatten.length &&
    allIdx (fun i e => Nat.beq i 0 ||
      (Nat.blt e.1.1 i && Nat.blt e.1.2 nl && actF e.1.2 (lookC B C e.1.1) == e.2)) 0
      (List.zip (List.zip par via) C.flatten) &&
    Nat.beq ord.length C.flatten.length && ord.all (fun i => Nat.blt i C.flatten.length) &&
    sortedLt (ord.map (lookC B C))

@[expose] def omOf (C : List (List (List Nat))) (rows : List (List Nat)) (par via : List Nat) :
    OmegaData (List Nat) :=
  ⟨C.flatten.toArray, (rows.map List.toArray).toArray, par.toArray, via.toArray⟩

@[expose] def omCodeC (n : Nat) (ts : Array (Array Nat)) (x0 : List Nat) (B : Nat)
    (C : List (List (List Nat))) (rows : List (List Nat)) (par via ord : List Nat) : Bool :=
  omC (fun l x => codeSetT n (ts.getD l #[]) x) x0 ts.size B C rows par via ord

end CFSG.KC.SLDc

end

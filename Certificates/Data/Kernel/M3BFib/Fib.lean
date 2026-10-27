module

public import Certificates.Data.Kernel.M3BFib.Kit

public section

namespace CFSG.KC.M3BF

open Timmesfeld.M3B (WT)

abbrev Ins := Nat × Nat × Nat

@[expose] noncomputable def insWT (ins : Ins) (acc : List WT) : WT :=
  Nat.rec (motive := fun _ => WT) (WT.gen ins.2.1)
    (fun n _ => Nat.rec (motive := fun _ => WT)
      (WT.mul (acc.getD ins.2.1 (WT.gen 0)) (acc.getD ins.2.2 (WT.gen 0)))
      (fun _ _ => WT.pow (acc.getD ins.2.1 (WT.gen 0)) ins.2.2) n) ins.1

@[expose] noncomputable def slpNodes (P : List Ins) : List WT :=
  List.rec (motive := fun _ => List WT) [] (fun ins _ acc => List.cons (insWT ins acc) acc) P

@[expose] noncomputable def slpWT (P : List Ins) : WT := (slpNodes P).headD (WT.gen 0)

@[expose] noncomputable def lane (x j : Nat) : Nat := Nat.mod (Nat.div x (Nat.pow 64 j)) 64

abbrev AffK := List Nat × Nat

@[expose] noncomputable def applyK (M : AffK) (p : Nat) : Nat := red (Nat.add (vm (dig3 p) M.1) M.2)

@[expose] noncomputable def pt0 (T : PD) : PD := (T.1, List.replicate 12 0, T.2.2)

@[expose] noncomputable def img0K (Lp : List Nat) (T G Gi : PD) : PD :=
  compK Lp (compK Lp Gi (pt0 T)) G

@[expose] noncomputable def affA (G Gi : PD) : List Nat :=
  (colsK (Gi.1.map dig3)).map (fun col => red (Nat.mul G.2.2 col))

@[expose] noncomputable def conjOK (Lp : List Nat) (T G Gi : PD) (M : AffK) : Bool :=
  (fun (I : PD) => I.1 == T.1 && I.2.2 == T.2.2 && (affA G Gi, enc I.2.1) == M)
    (img0K Lp T G Gi)

@[expose] noncomputable def goodPDb (D : PD) : Bool :=
  D.1.length == 12 && D.1.all (fun r => enc (dig3 r) == r) && D.2.1.length == 12

@[expose] noncomputable def genOne (Lp : List Nat) (T G Gi : PD) (M M' : AffK) : Bool :=
  goodPDb Gi && pdEq (compK Lp Gi G) oneK && conjOK Lp T G Gi M && conjOK Lp T Gi G M'

abbrev GenK := List Ins × PD × PD × AffK × AffK

@[expose] noncomputable def wordChk (Lp : List Nat) (L : List PD) (gs : List GenK) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun g _ ih => pdEq (adOfK Lp L (slpWT g.1)) g.2.1 && ih) gs

@[expose] noncomputable def genChk (Lp : List Nat) (T : PD) (gs : List GenK) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun g _ ih => genOne Lp T g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2 && ih) gs

@[expose] noncomputable def mapsOf (gs : List GenK) : List AffK :=
  List.rec (motive := fun _ => List AffK) [] (fun g _ ih => g.2.2.2.1 :: g.2.2.2.2 :: ih) gs

abbrev BasK := Nat × Nat × List Nat

@[expose] noncomputable def idRows : List Nat := (List.range 12).map (fun i => Nat.pow 64 i)

@[expose] noncomputable def combK (e ds : List Nat) : Nat := vm e ds

@[expose] noncomputable def transK (ms : List AffK) : List Nat :=
  (List.range 12).map (fun j => (ms.getD (Nat.mul 2 j) ([], 0)).2)

@[expose] noncomputable def cnt (j : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun a _ ih => bif a == j then Nat.succ ih else ih) l

@[expose] noncomputable def basisChk (ms : List AffK) (bs : List BasK) (fr : List Nat) : Bool :=
  (List.range 12).all (fun j => (ms.getD (Nat.mul 2 j) ([], 0)).1 == idRows) &&
  (List.range 12).all (fun j => Nat.add (cnt j fr) (cnt j (bs.map Prod.fst)) == 1) &&
  fr.all (fun j => Nat.blt j 12) &&
  bs.all (fun b => b.2.2.length == 12 && b.2.2.all (fun e => Nat.blt e 3) &&
    b.2.1 == red (combK b.2.2 (transK ms)) &&
    bs.all (fun b' => lane b.2.1 b'.1 == bif b'.1 == b.1 then 1 else 0))

@[expose] noncomputable def redW (bs : List BasK) (c : Nat) : Nat :=
  red (List.rec (motive := fun _ => Nat) c
    (fun b _ acc => Nat.add acc (Nat.mul (Nat.mod (Nat.sub 3 (lane c b.1)) 3) b.2.1)) bs)

@[expose] noncomputable def ptQ (fr : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun f _ ih n => Nat.add (Nat.mul (Nat.mod n 3) (Nat.pow 64 f)) (ih (Nat.div n 3))) fr i

@[expose] noncomputable def bit (m i : Nat) : Bool := Nat.mod (Nat.div m (Nat.pow 2 i)) 2 == 1

@[expose] noncomputable def rootMask (rs : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun r _ ih => Nat.lor ih (Nat.pow 2 r.2)) rs

@[expose] noncomputable def rowsK (ms : List AffK) (bs : List BasK) (fr : List Nat) (n : Nat)
    (rows : List (Nat × Nat × Nat)) (m : Nat) : Option Nat :=
  List.rec (motive := fun _ => Nat → Option Nat) (fun m => some m)
    (fun r _ ih m => bif Nat.blt r.1 n && bit m r.2.1 && Nat.blt r.2.2 ms.length &&
        redW bs (applyK (ms.getD r.2.2 ([], 0)) (ptQ fr r.1)) == ptQ fr r.2.1
      then ih (Nat.lor m (Nat.pow 2 r.1)) else none) rows m

@[expose] noncomputable def forestChk (ms : List AffK) (bs : List BasK) (fr : List Nat)
    (rs : List (Nat × Nat)) (rows : List (Nat × Nat × Nat)) : Bool :=
  (fun n => rs.all (fun r => Nat.blt r.2 n && enc (dig3 r.1) == r.1 && redW bs r.1 == ptQ fr r.2) &&
    rowsK ms bs fr n rows (rootMask rs) == some (Nat.sub (Nat.pow 2 n) 1)) (Nat.pow 3 fr.length)

end CFSG.KC.M3BF

end

module

public import Certificates.Data.Kernel.SmithEKM
public import Certificates.Data.SMod20RhoData

public section

namespace CFSG.SmithE.K

open CFSG.SmithE

@[expose] noncomputable def distC (c : Nat) : Nat :=
  if c == 21 then 0 else if c == 5 then 1 else if c == 1 then 2 else 3

@[expose] noncomputable def atLeastK (k : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih n => bif n == 0 then false else ih (n &&& (n - 1))) k

@[expose] noncomputable def dEntK (x c : Nat) : Bool :=
  (c == 0 || c == 1 || c == 5 || c == 21) && atLeastK 16 x == decide (distC c ≤ 1)

@[expose] noncomputable def dRowK (a m : Nat) : List Nat → List Nat → Bool :=
  fun P => List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun b _ ih Ms => dEntK (m &&& Ms.headD 0) (cntK 693 (a &&& b)) && ih Ms.tail) P

@[expose] noncomputable def dTailsK (n : Nat) : List Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => List Nat → List Nat → Bool) (fun _ _ => true)
    (fun _ ih P M => dRowK (P.headD 0) (M.headD 0) P M && ih P.tail M.tail) n

@[expose] noncomputable def dChunkK (P M : List Nat) (s n : Nat) : Bool :=
  dTailsK n (P.drop s) (M.drop s)

@[expose] noncomputable def rowXK (R a : Nat) (cs inv : List Nat) : Nat :=
  (List.range 21).foldl (fun x t =>
    x ^^^ bif R.testBit (distC (cntK 693 (a &&& cs.getD t 0))) then inv.getD t 0 else 0) 0

@[expose] noncomputable def rankBodyK (R : Nat) (rr cc inv rs cs : List Nat) : Bool :=
  rr.length == 21 && cc.length == 21 && inv.length == 21 && rr.all (· < 891) &&
    cc.all (· < 891) && (List.range 21).all fun s => rowXK R (rs.getD s 0) cs inv == 2 ^ s

@[expose] noncomputable def rankWitK (P : List Nat) (R : Nat) (rr cc inv : List Nat) : Bool :=
  rankBodyK R rr cc inv (rr.map fun i => P.getD i 0) (cc.map fun j => P.getD j 0)

@[expose] noncomputable def chkRankK (P : List Nat) : Bool :=
  rankRels.toList == [2, 4, 6, 10, 12, 14] && rankRows.toList.length == 6 &&
    rankCols.toList.length == 6 && rankInv.toList.length == 6 &&
    (List.range 6).all fun r => rankWitK P (rankRels.toList.getD r 0)
      (rankRows.toList.getD r #[]).toList (rankCols.toList.getD r #[]).toList
      (rankInv.toList.getD r #[]).toList

@[expose] noncomputable def chkSpanWK (W : List Nat) : Bool :=
  spanIdx.toList.length == 20 && spanCoef.toList.length == 20 && spanIdx.toList.all (· < 891) &&
    (List.range 20).all fun m =>
      applyCols (spanIdx.toList.map fun i => W.getD i 0).toArray (spanCoef.toList.getD m 0) == 2 ^ m

end CFSG.SmithE.K

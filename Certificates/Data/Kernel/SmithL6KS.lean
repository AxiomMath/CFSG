module

public import Certificates.Data.Kernel.SmithL6KF
public import Certificates.Data.Kernel.SmithEKS

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6.CollK (apK)
open CFSG.SmithE (insertVec reduceBy)
open CFSG.SmithE.K (applyL gensL coefR)

@[expose] def mulK (A B : List Nat) : List Nat := B.map (apK A)

@[expose] def sPairK (c0 : Nat) (A : List Nat) (q : Nat × List Nat) : Bool :=
  match kindC c0 q.1 with
  | 0 => mulK A q.2 == mulK q.2 A
  | 1 => mulK (mulK A q.2) A == mulK (mulK q.2 A) q.2
  | _ => let X := mulK A q.2; let Y := mulK q.2 A; mulK X X == mulK Y Y

@[expose] def sEchL (L : List Nat) : List (Nat × Nat) := (gensL L).foldl insertVec []

@[expose] def sSynL (E : List (Nat × Nat)) : List Nat :=
  (List.range 20).map fun m => reduceBy E (2 ^ m)

@[expose] def sSpanE (L : List Nat) (E : List (Nat × Nat)) : Bool :=
  let B := E.map (·.2)
  let S := (List.range 20).map fun m => reduceBy E (2 ^ m)
  E.length == 6 && (B.all fun b => applyL S b == 0) && (gensL L).all fun v => let c := coefR E v
    decide (c < 64) && applyL B c == v

@[expose] def sInt0E (B0 : List Nat) (W c0 c : Nat) (E : List (Nat × Nat)) : Bool :=
  let S := B0.map (apK (sSynL E))
  let h0 := kindC c0 c == 0
  (List.range 64).all fun d => apK S d != 0 ||
    (let v := apK B0 d; v == 0 || (h0 && W.testBit v))

@[expose] def sRowK (A B0 : List Nat) (W c0 : Nat) (q : Nat × List Nat) : Bool :=
  let E := sEchL q.2
  sPairK c0 A q && sSpanE q.2 E && sInt0E B0 W c0 q.1 E

@[expose] def sRowsK (C : List Nat) (L : List (List Nat)) (W lo n : Nat) : Bool :=
  (((C.zip L).drop lo).take n).all
    (sRowK (L.getD 0 []) ((sEchL (L.getD 0 [])).map (·.2)) W (C.getD 0 0))

end CFSG.SmithL6.K

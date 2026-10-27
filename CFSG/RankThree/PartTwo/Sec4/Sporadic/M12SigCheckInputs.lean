module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12SigData
public import CFSG.RankThree.PartTwo.Toolkit.M12Local
public meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12SigData
public meta import CFSG.RankThree.PartTwo.Toolkit.M12Local

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig

open CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12

@[expose] def tBp : List ℕ := [5, 8, 1, 0, 7, 3, 10, 9, 2, 4, 11, 6]

@[expose] def letterTb (l : Int) : List ℕ :=
  if l = 1 then tA else if l = -1 then tinv tA else if l = 2 then tBp else tinv tBp

@[expose] def wordTb : List Int → List ℕ
  | [] => tid
  | l :: w => tmul (letterTb l) (wordTb w)

@[expose] def tabb (i k : ℕ) : List ℕ := wordTb (wrd i k)

@[expose] def prodTb (k : Idx) : List ℕ :=
  tmul (tabb 0 k.1) (tmul (tabb 1 k.2.1) (tmul (tabb 2 k.2.2.1) (tmul (tabb 3 k.2.2.2.1)
    (tabb 4 k.2.2.2.2))))

@[expose] def tsq (t : List ℕ) : List ℕ := tmul t t

@[expose] def tsqIter : ℕ → List ℕ → List ℕ
  | 0, t => t
  | n + 1, t => tsqIter n (tsq t)

@[expose] def isTwo (t : List ℕ) : Bool := tsqIter 7 t == tid

@[expose] def isInvT (t : List ℕ) : Bool := tmul t t == tid && t != tid

@[expose] def commT (s t : List ℕ) : Bool := tmul t s == tmul s t

@[expose] def commConjAll (S : List (List ℕ)) (t : List ℕ) : Bool :=
  S.all fun e => commT (tconj e t) t

@[expose] def twoConjAll (S : List (List ℕ)) (t : List ℕ) : Bool :=
  S.all fun e => isTwo (tmul t (tconj e t))

@[expose] def aiT (i : ℕ) : List ℕ := tmul (tpow zT i) aT

@[expose] def idxC (i : ℕ) : List Idx := if i = 0 then idxC0 else if i = 1 then idxC1 else idxC2

@[expose] def idxV (i : ℕ) : List Idx := if i = 0 then idxV0 else if i = 1 then idxV1 else idxV2

@[expose] def VT (i : ℕ) : List (List ℕ) := (idxV i).map prodT

@[expose] def UT : List (List ℕ) := VT 0 ++ VT 1 ++ VT 2

@[expose] def vg1 (i : ℕ) : List ℕ := (VT i).getD 1 tid

@[expose] def vg2 (i : ℕ) : List ℕ := (VT i).getD 2 tid

@[expose] def xbT : List ℕ := wordTb wX

@[expose] def ybT : List ℕ := wordTb wY

@[expose] def zbT : List ℕ := tcm xbT ybT

@[expose] def abT : List ℕ := tmul xbT ybT

@[expose] def fPairs : List (List ℕ × List ℕ) :=
  (List.range 3).flatMap fun i => (List.range 3).map fun j =>
    (tmul (tpow zT i) (tpow aT j), tmul (tpow zbT i) (tpow abT j))

@[expose] def chkEF : Bool :=
  allIdx.all fun k => let t := prodT k; !isInvT t || (!commConjAll ET t && !commConjAll FT t)

@[expose] def chkInv : Bool :=
  allIdx.all fun k => let t := prodT k; !isInvT t || !commConjAll AT t || UT.contains t

@[expose] def chkV : Bool :=
  allIdx.all fun k => let t := prodT k;
    (List.range 3).all fun i =>
      !(commT (vg1 i) t && commT (vg2 i) t && isTwo t && twoConjAll AT t) || (VT i).contains t

@[expose] def chkOuter : Bool :=
  allIdx.all fun k => let g := prodT k; let gb := prodTb k;
    !isTwo (tmul g gb) || fPairs.any fun p => !isTwo (tmul (tmul (tmul g p.2) gb) (tinv p.1))

@[expose] def chkCent : Bool :=
  (allIdx.all fun k => (List.range 3).all fun i =>
      !predC [aiT i] (prodT k) || (idxC i).contains k) &&
    ((List.range 3).all fun i => (idxC i).all fun k => predC [aiT i] (prodT k)) &&
    ((List.range 3).all fun i => decide ((idxC i).map prodT).Nodup)

@[expose] def chkNormal : Bool :=
  (List.range 3).all fun i => (idxC i).all fun k =>
    (VT i).all fun v => (VT i).contains (tconj (prodT k) v)

@[expose] def chkVStruct : Bool :=
  (List.range 3).all fun i =>
    (VT i).contains tid && ((VT i).all fun s => (VT i).all fun t => (VT i).contains (tmul s t)) &&
    ((VT i).all fun s => (VT i).contains (tinv s)) && decide (VT i).Nodup &&
    (VT i).length == 4 && ((VT i).all fun s => commT (aiT i) s) &&
    (AT.all fun f => (VT i).all fun v => (VT i).contains (tconj f v)) &&
    ((VT i).all fun u => u == tid ||
      ((AT.any fun f => tconj f u == vg1 i) && (AT.any fun f => tconj f u == vg2 i))) &&
    ((List.range 3).all fun j => j == i || !(VT j).contains (vg1 i)) &&
    (P0T.all fun s => (List.range 3).any fun w =>
      (VT i).all fun v => (VT w).contains (tconj (tinv s) v)) &&
    ((List.range 3).all fun w => P0T.any fun s =>
      (VT i).all fun v => (VT w).contains (tconj (tinv s) v))

@[expose] def gamA : List (Bool × Idx) :=
  [(false, (4, 4, 9, 1, 1)), (true, (0, 0, 0, 4, 4)), (false, (10, 6, 0, 7, 6))]

@[expose] def gamB : List (Bool × Idx) :=
  [(true, (0, 0, 0, 2, 0)), (false, (3, 1, 9, 2, 2)), (true, (0, 0, 0, 2, 0)),
    (false, (3, 1, 9, 2, 2)), (true, (0, 0, 0, 0, 4)), (false, (11, 0, 1, 0, 2))]

@[expose] def gamProd (L : List (Bool × Idx)) : List ℕ :=
  L.foldr (fun p t => tmul (prodT p.2) t) tid

@[expose] def chkGamma : Bool :=
  ((gamA ++ gamB).all fun p => predP (if p.1 then zT else aT) (prodT p.2)) &&
    gamProd gamA == tA && gamProd gamB == tB

@[expose] def sigCheck : Bool :=
  chkEF && chkInv && chkV && chkOuter && chkCent && chkNormal && chkVStruct && chkGamma

end CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig

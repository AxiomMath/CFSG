module

public import CFSG.RankThree.PartTwo.Toolkit.M12Enum
public import CFSG.RankThree.PartTwo.Toolkit.PermTab
public import CFSG.RankThree.Asc83Table.Reduction
public meta import CFSG.RankThree.PartTwo.Toolkit.M12Enum
public meta import CFSG.RankThree.PartTwo.Toolkit.PermTab
public meta import CFSG.GH74.M12.HypCore
public meta import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.M12.Reductions
public meta import CFSG.GH74.M12.Reductions
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.RankThree.PartTwo.Toolkit.M12

open CFSG.GH74.M12.Hyp CFSG.Blueprint CFSG.RankThree.Asc83Table Subgroup

open CFSG.RankThree.PartTwo.Toolkit (toP3 toP4)

open scoped commutatorElement

@[expose] def tconj (t s : List ℕ) : List ℕ := tmul (tmul t s) (tinv t)

@[expose] def tcm (s t : List ℕ) : List ℕ := tmul (tmul (tmul s t) (tinv s)) (tinv t)

@[expose] def wX : List Int :=
  [1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1]

@[expose] def wY : List Int :=
  [1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2]

@[expose] def xT : List ℕ := wordT wX

@[expose] def yT : List ℕ := wordT wY

@[expose] def zT : List ℕ := tcm xT yT

@[expose] def aT : List ℕ := tmul xT yT

@[expose] def nf3T (u v w : List ℕ) : List (List ℕ) :=
  (List.range 3).flatMap fun i => (List.range 3).flatMap fun j => (List.range 3).map fun k =>
    tmul (tmul (tpow u i) (tpow v j)) (tpow w k)

@[expose] def nf2T (u v : List ℕ) : List (List ℕ) :=
  (List.range 3).flatMap fun i => (List.range 3).map fun j => tmul (tpow u i) (tpow v j)

@[expose] def idxNP : List Idx :=
  [(0, 0, 0, 0, 0), (0, 0, 0, 0, 4), (0, 0, 0, 1, 0), (0, 0, 0, 1, 4), (0, 0, 0, 2, 0),
  (0, 0, 0, 2, 4), (0, 0, 0, 3, 0), (0, 0, 0, 3, 4), (0, 0, 0, 4, 0), (0, 0, 0, 4, 4),
  (0, 0, 0, 5, 0), (0, 0, 0, 5, 4), (0, 0, 0, 6, 0), (0, 0, 0, 6, 4), (0, 0, 0, 7, 0),
  (0, 0, 0, 7, 4), (0, 0, 0, 8, 0), (0, 0, 0, 8, 4), (0, 1, 3, 0, 3), (0, 1, 3, 0, 7),
  (0, 1, 3, 1, 3), (0, 1, 3, 1, 7), (0, 1, 3, 2, 3), (0, 1, 3, 2, 7), (0, 1, 3, 3, 3),
  (0, 1, 3, 3, 7), (0, 1, 3, 4, 3), (0, 1, 3, 4, 7), (0, 1, 3, 5, 3), (0, 1, 3, 5, 7),
  (0, 1, 3, 6, 3), (0, 1, 3, 6, 7), (0, 1, 3, 7, 3), (0, 1, 3, 7, 7), (0, 1, 3, 8, 3),
  (0, 1, 3, 8, 7), (1, 0, 6, 0, 3), (1, 0, 6, 0, 7), (1, 0, 6, 1, 3), (1, 0, 6, 1, 7),
  (1, 0, 6, 2, 3), (1, 0, 6, 2, 7), (1, 0, 6, 3, 3), (1, 0, 6, 3, 7), (1, 0, 6, 4, 3),
  (1, 0, 6, 4, 7), (1, 0, 6, 5, 3), (1, 0, 6, 5, 7), (1, 0, 6, 6, 3), (1, 0, 6, 6, 7),
  (1, 0, 6, 7, 3), (1, 0, 6, 7, 7), (1, 0, 6, 8, 3), (1, 0, 6, 8, 7), (1, 7, 8, 0, 2),
  (1, 7, 8, 0, 5), (1, 7, 8, 1, 2), (1, 7, 8, 1, 5), (1, 7, 8, 2, 2), (1, 7, 8, 2, 5),
  (1, 7, 8, 3, 2), (1, 7, 8, 3, 5), (1, 7, 8, 4, 2), (1, 7, 8, 4, 5), (1, 7, 8, 5, 2),
  (1, 7, 8, 5, 5), (1, 7, 8, 6, 2), (1, 7, 8, 6, 5), (1, 7, 8, 7, 2), (1, 7, 8, 7, 5),
  (1, 7, 8, 8, 2), (1, 7, 8, 8, 5), (2, 6, 8, 0, 2), (2, 6, 8, 0, 5), (2, 6, 8, 1, 2),
  (2, 6, 8, 1, 5), (2, 6, 8, 2, 2), (2, 6, 8, 2, 5), (2, 6, 8, 3, 2), (2, 6, 8, 3, 5),
  (2, 6, 8, 4, 2), (2, 6, 8, 4, 5), (2, 6, 8, 5, 2), (2, 6, 8, 5, 5), (2, 6, 8, 6, 2),
  (2, 6, 8, 6, 5), (2, 6, 8, 7, 2), (2, 6, 8, 7, 5), (2, 6, 8, 8, 2), (2, 6, 8, 8, 5),
  (2, 8, 2, 0, 3), (2, 8, 2, 0, 7), (2, 8, 2, 1, 3), (2, 8, 2, 1, 7), (2, 8, 2, 2, 3),
  (2, 8, 2, 2, 7), (2, 8, 2, 3, 3), (2, 8, 2, 3, 7), (2, 8, 2, 4, 3), (2, 8, 2, 4, 7),
  (2, 8, 2, 5, 3), (2, 8, 2, 5, 7), (2, 8, 2, 6, 3), (2, 8, 2, 6, 7), (2, 8, 2, 7, 3),
  (2, 8, 2, 7, 7), (2, 8, 2, 8, 3), (2, 8, 2, 8, 7)]

@[expose] def idxCE : List Idx :=
  [(0, 0, 0, 0, 0), (0, 0, 0, 1, 4), (0, 0, 0, 2, 4), (0, 0, 0, 3, 0), (0, 0, 0, 4, 0),
  (0, 0, 0, 5, 0), (0, 0, 0, 6, 4), (0, 0, 0, 7, 4), (0, 0, 0, 8, 0)]

@[expose] def idxCF : List Idx :=
  [(0, 0, 0, 0, 0), (0, 0, 0, 1, 4), (0, 0, 0, 5, 0), (1, 0, 6, 1, 7), (1, 0, 6, 2, 7),
  (1, 0, 6, 6, 7), (2, 6, 8, 0, 2), (2, 6, 8, 3, 2), (2, 6, 8, 6, 5)]

@[expose] def idxNA : List Idx :=
  [(0, 0, 0, 0, 0), (0, 0, 0, 1, 4), (0, 0, 0, 2, 4), (0, 0, 0, 3, 0), (0, 0, 0, 4, 0),
  (0, 0, 0, 5, 0), (0, 0, 0, 6, 4), (0, 0, 0, 7, 4), (0, 0, 0, 8, 0), (0, 1, 3, 0, 7),
  (0, 1, 3, 1, 3), (0, 1, 3, 2, 3), (0, 1, 3, 3, 7), (0, 1, 3, 4, 7), (0, 1, 3, 5, 7),
  (0, 1, 3, 6, 3), (0, 1, 3, 7, 3), (0, 1, 3, 8, 7), (1, 0, 6, 0, 3), (1, 0, 6, 1, 7),
  (1, 0, 6, 2, 7), (1, 0, 6, 3, 3), (1, 0, 6, 4, 3), (1, 0, 6, 5, 3), (1, 0, 6, 6, 7),
  (1, 0, 6, 7, 7), (1, 0, 6, 8, 3), (1, 7, 8, 0, 2), (1, 7, 8, 1, 5), (1, 7, 8, 2, 5),
  (1, 7, 8, 3, 2), (1, 7, 8, 4, 2), (1, 7, 8, 5, 2), (1, 7, 8, 6, 5), (1, 7, 8, 7, 5),
  (1, 7, 8, 8, 2), (2, 6, 8, 0, 2), (2, 6, 8, 1, 5), (2, 6, 8, 2, 5), (2, 6, 8, 3, 2),
  (2, 6, 8, 4, 2), (2, 6, 8, 5, 2), (2, 6, 8, 6, 5), (2, 6, 8, 7, 5), (2, 6, 8, 8, 2),
  (2, 8, 2, 0, 7), (2, 8, 2, 1, 3), (2, 8, 2, 2, 3), (2, 8, 2, 3, 7), (2, 8, 2, 4, 7),
  (2, 8, 2, 5, 7), (2, 8, 2, 6, 3), (2, 8, 2, 7, 3), (2, 8, 2, 8, 7)]

@[expose] def idxCA : List Idx :=
  [(0, 0, 0, 0, 0), (0, 0, 0, 1, 4), (0, 0, 0, 5, 0), (1, 0, 6, 3, 3), (1, 0, 6, 5, 3),
  (1, 0, 6, 7, 7), (2, 6, 8, 1, 5), (2, 6, 8, 7, 5), (2, 6, 8, 8, 2)]

@[expose] def idxNa : List Idx :=
  [(0, 0, 0, 0, 0), (0, 0, 0, 1, 4), (0, 0, 0, 5, 0), (0, 1, 3, 1, 3), (0, 1, 3, 2, 3),
  (0, 1, 3, 6, 3), (1, 0, 6, 3, 3), (1, 0, 6, 5, 3), (1, 0, 6, 7, 7), (1, 7, 8, 0, 2),
  (1, 7, 8, 3, 2), (1, 7, 8, 6, 5), (2, 6, 8, 1, 5), (2, 6, 8, 7, 5), (2, 6, 8, 8, 2),
  (2, 8, 2, 0, 7), (2, 8, 2, 4, 7), (2, 8, 2, 8, 7), (3, 1, 9, 2, 2), (3, 1, 9, 4, 5),
  (3, 1, 9, 5, 5), (3, 10, 0, 0, 5), (3, 10, 0, 3, 5), (3, 10, 0, 6, 2), (4, 4, 9, 1, 1),
  (4, 4, 9, 3, 6), (4, 4, 9, 4, 6), (4, 9, 9, 1, 2), (4, 9, 9, 7, 2), (4, 9, 9, 8, 5),
  (5, 8, 8, 1, 1), (5, 8, 8, 3, 6), (5, 8, 8, 4, 6), (5, 10, 6, 4, 4), (5, 10, 6, 6, 0),
  (5, 10, 6, 7, 0), (6, 1, 6, 0, 6), (6, 1, 6, 2, 1), (6, 1, 6, 7, 1), (6, 4, 6, 0, 1),
  (6, 4, 6, 2, 6), (6, 4, 6, 7, 6), (7, 3, 9, 4, 0), (7, 3, 9, 6, 4), (7, 3, 9, 7, 4),
  (7, 6, 9, 4, 4), (7, 6, 9, 6, 0), (7, 6, 9, 7, 0), (8, 7, 5, 0, 2), (8, 7, 5, 3, 2),
  (8, 7, 5, 6, 5), (8, 9, 0, 1, 1), (8, 9, 0, 3, 6), (8, 9, 0, 4, 6), (9, 3, 9, 1, 6),
  (9, 3, 9, 3, 1), (9, 3, 9, 4, 1), (9, 6, 9, 1, 5), (9, 6, 9, 7, 5), (9, 6, 9, 8, 2),
  (10, 1, 5, 5, 1), (10, 1, 5, 6, 6), (10, 1, 5, 8, 1), (10, 6, 0, 0, 1), (10, 6, 0, 2, 6),
  (10, 6, 0, 7, 6), (11, 0, 1, 0, 2), (11, 0, 1, 3, 2), (11, 0, 1, 6, 5), (11, 2, 9, 5, 1),
  (11, 2, 9, 6, 6), (11, 2, 9, 8, 1)]


@[expose] def P0T : List (List ℕ) := nf3T xT yT zT

@[expose] def ET : List (List ℕ) := nf2T zT xT

@[expose] def FT : List (List ℕ) := nf2T zT yT

@[expose] def AT : List (List ℕ) := nf2T zT aT

@[expose] def predN (gens S : List (List ℕ)) (t : List ℕ) : Bool :=
  gens.all fun s => S.contains (tconj t s)

@[expose] def predC (gens : List (List ℕ)) (t : List ℕ) : Bool :=
  gens.all fun s => tmul t s == tmul s t

@[expose] def predP (u t : List ℕ) : Bool := tconj t u == u || tconj t u == tpow u 2

@[expose] def enumData : List ((List ℕ → Bool) × List Idx) :=
  [(predN [xT, yT] P0T, idxNP), (predC [zT, xT], idxCE), (predC [zT, yT], idxCF),
    (predN [zT, aT] AT, idxNA), (predC [zT, aT], idxCA), (predP aT, idxNa)]

@[expose] def rowOf : List ℕ := [0, 1, 2, 0, 0, 1, 1, 2, 0, 2, 2, 1]

@[expose] def colOf : List ℕ := [0, 0, 0, 1, 2, 1, 2, 3, 3, 1, 2, 3]

@[expose] def rowTab (t : List ℕ) : List ℕ :=
  [rowOf.getD (t.getD 0 0) 0, rowOf.getD (t.getD 1 0) 0, rowOf.getD (t.getD 2 0) 0]

@[expose] def colTab (t : List ℕ) : List ℕ :=
  [colOf.getD (t.getD 0 0) 0, colOf.getD (t.getD 3 0) 0, colOf.getD (t.getD 4 0) 0,
    colOf.getD (t.getD 7 0) 0]

@[expose] def psiT (t : List ℕ) : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 4) :=
  (toP3 (rowTab t), toP4 (colTab t))

@[expose] def chkComplete : Bool :=
  allIdx.all fun k => enumData.all fun p => !p.1 (prodT k) || p.2.contains k

@[expose] def chkSound : Bool := enumData.all fun p => p.2.all fun k => p.1 (prodT k)

@[expose] def chkNodup : Bool := enumData.all fun p => decide (p.2.map prodT).Nodup

@[expose] def chkNP : Bool :=
  idxNP.all fun k => P0T.contains (tmul (prodT k) (prodT k)) && predN [zT, xT] ET (prodT k) &&
    predN [zT, yT] FT (prodT k)

@[expose] def chkNPcomm : Bool :=
  idxNP.all fun k => idxNP.all fun k' => P0T.contains (tcomm (prodT k) (prodT k'))

@[expose] def chkPsi : Bool :=
  (idxNa.all fun k => idxNa.all fun k' =>
    psiT (tmul (prodT k) (prodT k')) == psiT (prodT k) * psiT (prodT k')) &&
  (idxNa.all fun k => idxNa.all fun k' => psiT (prodT k) != psiT (prodT k') || k == k') &&
  (idxNa.all fun k => decide (Equiv.Perm.sign (psiT (prodT k)).2 = 1))

@[expose] def m12Check : Bool := chkComplete && chkSound && chkNodup && chkNP && chkNPcomm && chkPsi

end CFSG.RankThree.PartTwo.Toolkit.M12

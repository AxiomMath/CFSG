module

public import CFSG.LieType.Multipliers.CoverWords

public section

namespace CFSG.Sporadic.Recognition.McLMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Th.Native CFSG.Sporadic.McL.Native
  CFSG.Sporadic.VecOrbit.Native CFSG.F3.Native

@[expose] def invW (w : List ℤ) : List ℤ := (w.map Neg.neg).reverse

@[expose] def mclPos (c : List ℕ) : List (Fin 6 × Bool) :=
  c.map fun x => (⟨x % 6, Nat.mod_lt _ (by norm_num)⟩, true)

@[expose] def letterZ (l : Fin 6 × Bool) : ℤ :=
  if l.2 then (l.1.val : ℤ) + 1 else -((l.1.val : ℤ) + 1)

@[expose] def mclLabel (i j : ℕ) : ℕ :=
  if i = 0 ∧ j = 1 then 3 else if i = 1 ∧ j = 2 then 5 else if i = 2 ∧ j = 3 then 3
  else if i = 3 ∧ j = 5 then 3 else if i = 4 ∧ j = 5 then 6 else if i = 0 ∧ j = 4 then 4
  else if i = 2 ∧ j = 4 then 3 else if i = 2 ∧ j = 5 then 4 else 2

@[expose] def mclCoxeter : List (List (Fin 6 × Bool)) :=
  (List.finRange 6).map (fun i => [(i, true), (i, true)]) ++
    (List.finRange 6).flatMap fun i => ((List.finRange 6).filter fun j => i.val < j.val).map
      fun j => (List.replicate (mclLabel i.val j.val) [(i, true), (j, true)]).flatten

@[expose] def mclR0 : List (Fin 6 × Bool) := mclPos (List.replicate 7 [2, 4, 5]).flatten

@[expose] def mclExtra : List (List (Fin 6 × Bool)) :=
  [mclPos [0, 2, 5, 2, 5], mclPos [1, 4, 5, 4, 5, 4, 5],
    mclPos (List.replicate 3 [4, 0, 1]).flatten, mclPos (List.replicate 5 [1, 2, 4]).flatten,
    mclPos (List.replicate 4 [0, 4, 2, 3]).flatten, mclR0,
    mclPos (List.replicate 5 [1, 2, 3]).flatten]

@[expose] def mclRels : List (List (Fin 6 × Bool)) := mclCoxeter ++ mclExtra

@[expose] def mclCommCodes : Fin 6 → List (List ℕ × List ℕ)
  | 0 => [([2], [5])]
  | 1 => [([0], [1]), ([2], [5])]
  | 2 => [([1], [0]), ([5, 2, 1, 2], [1])]
  | 3 => [([1], [2]), ([1, 3], [2, 1, 2])]
  | 4 => [([1], [0, 4, 0])]
  | 5 => [([2], [1]), ([3, 2, 1, 2], [1, 0, 3, 5])]

@[expose] def mclComm (i : Fin 6) : List (List (Fin 6 × Bool) × List (Fin 6 × Bool)) :=
  (mclCommCodes i).map fun p => (mclPos p.1, mclPos p.2)

@[expose] def mclCommWord (i : Fin 6) : List (Fin 6 × Bool) := commWords (mclComm i)

@[expose] def mclCommW (i : Fin 6) : FreeGroup (Fin 6) := FreeGroup.mk (mclCommWord i)

abbrev mclCover : List (List (Fin 6 × Bool)) := coverWords mclRels mclCommWord

abbrev MclCover : Type := PresentedCover (wordSet mclRels) mclCommW

abbrev mclRels5 := restrictWords (subsetOf _ [0, 1, 2, 3, 5]) mclRels

abbrev mclCover5 := restrictWords (subsetOf _ [0, 1, 2, 3, 5]) mclCover

@[expose] def mclGenWord : ℕ → List ℤ
  | 0 =>
    [2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, 2, -1, -2]
  | 1 =>
    [2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, -2, -2, -1, -2, -2, -1, -2, -2, -1, -2]
  | 2 =>
    [-2, 1, 2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 2, 1, -2, 1, 2, -1, -2, -2, -1, -2, -1, -2, -2, -1, 2,
     -1, -2, -1, 2]
  | 3 =>
    [2, 1, 2, 2, 1, -2, 1, -2, -2, 1, 2, 2, -1, 2, -1, -2, -2, -1, -2]
  | 4 =>
    [2, 1, 2, 1, -2, -2, 1, 2, 2, -1, -2, -1, -2]
  | 5 =>
    [1]
  | _ => []

@[expose] def mclSurjA : List (Fin 6 × Bool) := mclPos [5]

@[expose] def mclSurjB : List (Fin 6 × Bool) := mclPos
    [4, 2, 5, 4, 2, 3, 5, 4, 2, 5, 4, 3, 2, 5, 4, 5, 2, 4, 5, 3]

@[expose] def mclT (O : VOrbit) (k : ℕ) : Table := wordT 275 (genTables O) (mclGenWord k)

@[expose] def mclV (O : VOrbit) (k : ℕ) : Table := invT 275 (mclT O k)

@[expose] def mclL (O : VOrbit) (z : ℤ) : Table :=
  if 0 < z then mclT O (z - 1).toNat else mclV O (-z - 1).toNat

@[expose] def mclTabRels : List (List ℤ) :=
  (mclRels ++ (List.finRange 6).map fun i => (i, false) :: mclCommWord i).map (List.map letterZ)

@[noinline, expose] def mclTabCheck : Bool :=
  let O := orbitData ()
  (List.range 6).all (fun k => invOK 275 (mclT O k) (mclV O k)) &&
    mclTabRels.all (fun r => wordT 275 (mclL O) r == idT 275) &&
    wordT 275 (mclL O) (mclSurjA.map letterZ) == O.alpha &&
    wordT 275 (mclL O) (mclSurjB.map letterZ) == O.beta

@[expose] def mclAText : String :=
  "1     3    42    42\n\
   010000000000000000000000000000000000000000\n\
   100000000000000000000000000000000000000000\n\
   000100000000000000000000000000000000000000\n\
   001000000000000000000000000000000000000000\n\
   000000100000000000000000000000000000000000\n\
   000000001000000000000000000000000000000000\n\
   000010000000000000000000000000000000000000\n\
   000000000001000000000000000000000000000000\n\
   000001000000000000000000000000000000000000\n\
   000000000000010000000000000000000000000000\n\
   000000000000000100000000000000000000000000\n\
   000000010000000000000000000000000000000000\n\
   002110210202110000000000000000000000000000\n\
   000000000100000000000000000000000000000000\n\
   121200020101021000000000000000000000000000\n\
   000000000010000000000000000000000000000000\n\
   001201012212010210000000000000000000000000\n\
   011120200222002120220000000000000000000000\n\
   002110220011000200100000000000000000000000\n\
   010212001022022122200000000000000000000000\n\
   021022011120001111111000000000000000000000\n\
   000000000000000000000010000000000000000000\n\
   000000000000000000000100000000000000000000\n\
   000000000000000000000000100000000000000000\n\
   000000000000000000000001000000000000000000\n\
   000000000000000000000000000100000000000000\n\
   000000000000000000000000000001000000000000\n\
   000000000000000000000000010000000000000000\n\
   000000000000000000000000000000001000000000\n\
   000000000000000000000000001000000000000000\n\
   000000000000000000000000000000000010000000\n\
   000000000000000000000000000000000000100000\n\
   000000000000000000000000000010000000000000\n\
   000000000000000000000002110210202110000000\n\
   000000000000000000000000000000100000000000\n\
   000000000000000000000121200020101021000000\n\
   000000000000000000000000000000010000000000\n\
   000000000000000000000001201012212010210000\n\
   000000000000000000000011120200222002120220\n\
   000000000000000000000002110220011000200100\n\
   000000000000000000000010212001022022122200\n\
   000000000000000000000021022011120001111111"

@[expose] def mclBText : String :=
  "1     3    42    42\n\
   001000000000000000000000000000000000000000\n\
   100000000000000000000000000000000000000000\n\
   000010000000000000000000000000000000000000\n\
   000001000000000000000000000000000000000000\n\
   000000010000000000000000000000000000000000\n\
   000000000100000000000000000000000000000000\n\
   000000000010000000000000000000000000000000\n\
   010000000000000000000000000000000000000000\n\
   000000000000100000000000000000000000000000\n\
   000000000000001000000000000000000000000000\n\
   000000000000000010000000000000000000000000\n\
   000000000000000001000000000000000000000000\n\
   000000000000000000100000000000000000000000\n\
   000000000000000000010000000000000000000000\n\
   000202000200002000000000000000000000000000\n\
   000000000000000000001000000000000000000000\n\
   211011011221220010021000000000000000000000\n\
   001020101012201100101000000000000000000000\n\
   121021001022202220122000000000000000000000\n\
   200222222121012220212000000000000000000000\n\
   221210110202100202010000000000000000000000\n\
   000000000000021210112001000000000000000000\n\
   100000000000021010200100000000000000000000\n\
   000000000002222021012000010000000000000000\n\
   000000000002022102210000001000000000000000\n\
   000000000002202001102000000010000000000000\n\
   000000000002102101002000000000100000000000\n\
   000000000000001011020000000000010000000000\n\
   000000000001200122200010000000000000000000\n\
   000000000001000102222000000000000100000000\n\
   000000000001002010100000000000000001000000\n\
   000000000001002001010000000000000000010000\n\
   000000000002001221110000000000000000001000\n\
   000000000001100111121000000000000000000100\n\
   000000000000200122202000000000000000000010\n\
   000000000001201200011000202000200002000000\n\
   000000000002202021011000000000000000000001\n\
   200000000000110211100211011011221220010021\n\
   000000000001122001120001020101012201100101\n\
   100000000002120112122121021001022202220122\n\
   200000000001221201100200222222121012220212\n\
   200000000002010100102221210110202100202010"

@[expose] def mclA3 : Array V := rowsOf 42 mclAText

@[expose] def mclB3 : Array V := rowsOf 42 mclBText

@[expose] def mclAB (z : ℤ) : Array V :=
  if z = 1 ∨ z = -1 then mclA3 else if z = 2 then mclB3 else powM 42 mclB3 4

@[expose] def mclWordM (w : List ℤ) : Array V := w.foldr (fun l X => mul 42 (mclAB l) X) (idM 42)

@[expose] def mclEvalM (E Ei : ℕ → Array V) (w : List (Fin 6 × Bool)) : Array V :=
  w.foldr (fun l X => mul 42 (if l.2 then E l.1.val else Ei l.1.val) X) (idM 42)

@[expose] def mclYs : Array (Array V) := Array.ofFn (n := 6) fun k => mclWordM (mclGenWord k.val)

@[expose] def mclYis : Array (Array V) :=
  Array.ofFn (n := 6) fun k => mclWordM (invW (mclGenWord k.val))

@[expose] def mclEs : Array (Array V) :=
  Array.ofFn (n := 6) fun i => mclEvalM (fun k => mclYs[k]!) (fun k => mclYis[k]!) (mclCommWord i)

@[expose] def mclEis : Array (Array V) :=
  Array.ofFn (n := 6) fun i =>
    mclEvalM (fun k => mclYs[k]!) (fun k => mclYis[k]!) (FreeGroup.invRev (mclCommWord i))

@[expose] def mclMatCheckOf (E Ei : ℕ → Array V) : Bool :=
  (List.range 6).all (fun i => canonM 42 (E i) && canonM 42 (Ei i) &&
      eqM 42 (mul 42 (E i) (Ei i)) (idM 42) && eqM 42 (mul 42 (Ei i) (E i)) (idM 42)) &&
    mclCover.all (fun w => eqM 42 (mclEvalM E Ei w) (idM 42)) &&
    canonM 42 (mclEvalM E Ei mclR0) && !eqM 42 (mclEvalM E Ei mclR0) (idM 42) &&
    eqM 42 (mul 42 (mclEvalM E Ei mclR0) (mul 42 (mclEvalM E Ei mclR0)
      (mclEvalM E Ei mclR0))) (idM 42)

@[noinline, expose] def mclMatCheck : Bool :=
  let Es := mclEs
  let Eis := mclEis
  mclMatCheckOf (fun i => Es[i]!) (fun i => Eis[i]!)

end CFSG.Sporadic.Recognition.McLMultiplier

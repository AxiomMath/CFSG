module

public import Certificates.Data.SmithD6Model
public import Certificates.Data.SmithD6Stab

public noncomputable section

namespace CFSG.SmithD6

set_option compiler.extract_closed false

@[expose] def mf7ApAux (cols : Array Nat) (c : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => mf7ApAux cols c k ^^^ (if c.testBit k then cols[k]! else 0)

@[expose] def mf7Ap (cols : Array Nat) (c : Nat) : Nat := mf7ApAux cols c cols.size

theorem mf7ApAux_eq (cols : Array Nat) (c n : Nat) :
    mf7ApAux cols c n =
      (List.range n).foldl (fun acc m => if c.testBit m then acc ^^^ cols[m]! else acc) 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [mf7ApAux, List.range_succ, List.foldl_append, ← ih]
    by_cases h : c.testBit k
    · simp [h]
    · simp [h]

theorem mf7Ap_eq (cols : Array Nat) (c : Nat) : mf7Ap cols c = applyCols cols c := by
  unfold mf7Ap applyCols
  exact mf7ApAux_eq cols c cols.size

@[expose] def mf7All (n : Nat) (p : Nat → Bool) : Bool := Id.run do
  for i in [0:n] do
    if !p i then return false
  return true

@[expose] def mf7Any (n : Nat) (p : Nat → Bool) : Bool := Id.run do
  for i in [0:n] do
    if p i then return true
  return false

@[expose] def mf7Count (n : Nat) (p : Nat → Bool) : Nat := Id.run do
  let mut c := 0
  for i in [0:n] do
    if p i then c := c + 1
  return c

@[expose] def e4f7Bfs (n m : Nat) (f : Nat → Nat → Nat) (root : Nat) :
    Array Nat × Array Nat :=
  Id.run do
    let mut par := (Array.replicate n n).set! root root
    let mut gen := Array.replicate n 0
    let mut queue : Array Nat := #[root]
    let mut head := 0
    for _ in [0:n] do
      if head < queue.size then
        let u := queue[head]!
        head := head + 1
        for g in [0:m] do
          let v := f g u
          if v < n && par[v]! == n then
            par := par.set! v u
            gen := gen.set! v g
            queue := queue.push v
    return (par, gen)

@[expose] def e4f7TreeWord (par gen : Array Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, v => if par[v]! == v then [] else gen[v]! :: e4f7TreeWord par gen fuel par[v]!

@[expose] def mf7IsWt (v : Nat) : Bool := let j := wtIdx v; decide (j < 75735) && wt j == v

@[expose] def mf7ChkWt (_ : Unit := ()) : Bool :=
  mf7All 75735 (fun j => wtIdx (wt j) == j) &&
  mf7All 75735 (fun i => wt i != 0 && wt i < 4294967296) &&
  mf7All 75735 fun i => mf7Any 75735 fun j => adjW i j && wt j != wt i

@[expose] def mf7ChkTvAdj0 (_ : Unit := ()) : Bool :=
  let A := tvCols 0
  mf7All 75735 fun i =>
    let v := mf7Ap A (wt i)
    let j := wtIdx v
    decide (j < 75735) && wt j == v && adjW i j

theorem mf7_wt_wtIdx (x : Nat) (h : wtIdx x < 75735) : wt (wtIdx x) = x := by
  dsimp only [wtIdx] at h ⊢
  generalize lowerBoundGo wtArr x 40 0 wtArr.size = i at h ⊢
  split at h
  · split
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      exact hc.2
    · contradiction
  · exact absurd h (Nat.lt_irrefl _)

theorem mf7_adjW_eq (a b : Nat) : adjW a b = (wt a == wt b || mf7IsWt (wt a ^^^ wt b)) := by
  unfold adjW mf7IsWt
  dsimp only
  by_cases h : wtIdx (wt a ^^^ wt b) < 75735
  · simp [h, mf7_wt_wtIdx _ h]
  · simp [h]

@[expose] def mf7Commute (A B : Array Nat) : Bool :=
  mf7All 32 fun m => mf7Ap A B[m]! == mf7Ap B A[m]!

@[expose] def mf7Braid (A B : Array Nat) : Bool :=
  mf7All 32 fun m => mf7Ap A (mf7Ap B A[m]!) == mf7Ap B (mf7Ap A B[m]!)

@[expose] def mf7Dih (A B : Array Nat) : Bool :=
  mf7All 32 fun m =>
    mf7Ap A (mf7Ap B (mf7Ap A B[m]!)) == mf7Ap B (mf7Ap A (mf7Ap B A[m]!))

@[expose] def mf7KindOf (A B : Array Nat) : Nat :=
  if mf7Commute A B then 0 else if mf7Braid A B then 1 else 2

@[expose] def mf7PairKind (k l : Nat) : Nat := mf7KindOf (tvCols k) (tvCols l)

theorem mf7KindOf_mem (A B : Array Nat) :
    mf7KindOf A B = 0 ∨ mf7KindOf A B = 1 ∨ mf7KindOf A B = 2 := by
  unfold mf7KindOf
  by_cases h1 : mf7Commute A B = true
  · simp [h1]
  · by_cases h2 : mf7Braid A B = true
    · simp [h1, h2]
    · simp [h1, h2]

theorem mf7PairKind_mem (k l : Nat) :
    mf7PairKind k l = 0 ∨ mf7PairKind k l = 1 ∨ mf7PairKind k l = 2 :=
  mf7KindOf_mem (tvCols k) (tvCols l)

@[expose] def mf7RelOf (k : Nat) (A B : Array Nat) : Bool :=
  match k with
  | 0 => mf7Commute A B
  | 1 => mf7Braid A B && !mf7Commute A B
  | _ => mf7Dih A B && !mf7Commute A B && !mf7Braid A B

@[expose] def mf7Gens (T : Array Nat) : Array Nat :=
  Array.ofFn (n := 32) fun m => T[m.val]! ^^^ 2 ^ m.val

@[expose] def mf7LowBit (r : Nat) : Nat := Nat.log2 (r &&& (r ^^^ (r - 1)))

@[expose] def mf7ReduceBy (E : List (Nat × Nat)) (v : Nat) : Nat :=
  E.foldl (fun v be => if v.testBit be.1 then v ^^^ be.2 else v) v

@[expose] def mf7InsertVec (E : List (Nat × Nat)) (g : Nat) : List (Nat × Nat) :=
  let r := mf7ReduceBy E g
  if r == 0 then E else
    let b := mf7LowBit r
    (E.map fun be => if be.2.testBit b then (be.1, be.2 ^^^ r) else be) ++ [(b, r)]

@[expose] def mf7Echelon (T : Array Nat) : List (Nat × Nat) :=
  (mf7Gens T).toList.foldl mf7InsertVec []

structure Mf7Span where
  basis : Array Nat
  coef : Array Nat
  syn : Array Nat
deriving Inhabited

@[expose] def mf7SpanData (T : Array Nat) : Mf7Span :=
  let E := mf7Echelon T
  { basis := (E.map (·.2)).toArray
    coef := (mf7Gens T).map fun v => (List.range E.length).foldl
      (fun acc i => if v.testBit (E[i]!).1 then acc + 2 ^ i else acc) 0
    syn := Array.ofFn (n := 32) fun m => mf7ReduceBy E (2 ^ m.val) }

@[expose] def mf7SpanOK (T : Array Nat) (D : Mf7Span) : Bool :=
  let g := mf7Gens T
  D.basis.size == 8 && D.coef.size == 32 &&
  mf7All 32 fun m => decide (D.coef[m]! < 256) &&
    mf7Ap D.basis D.coef[m]! == g[m]! && mf7Ap D.syn g[m]! == 0

@[expose] def mf7IntOK (A B : Array Nat) (Dl D0 : Mf7Span) : Bool :=
  let S := D0.basis.map (mf7Ap Dl.syn)
  let h0 := mf7Commute A B
  mf7All 256 fun d => mf7Ap S d != 0 ||
    (let v := mf7Ap D0.basis d; v == 0 || (h0 && mf7IsWt v))

def mf7Reps : Array Nat := #[0, 1, 31, 1579, 1607, 31899]

def mf7RepKinds : Array Nat := #[0, 0, 0, 0, 2, 1]

@[expose] def mf7ChkReps (_ : Unit := ()) : Bool :=
  let A := tvCols 0
  let D0 := mf7SpanData A
  mf7SpanOK A D0 &&
  mf7All 6 fun c =>
    let B := tvCols mf7Reps[c]!
    let Dl := mf7SpanData B
    mf7KindOf A B == mf7RepKinds[c]! && mf7RelOf mf7RepKinds[c]! A B &&
    (c == 0 || (mf7SpanOK B Dl && mf7IntOK A B Dl D0))

@[expose] def mf7ChkRepCls (_ : Unit := ()) : Bool :=
  mf7All 6 fun c => decide (mf7Reps[c]! < 365211) && stabCls (mf7Reps[c]!) == c

def e4f7Gens : Array Nat := #[1579, 7907, 1663, 234203]

@[expose] def e4f7GenCols (_ : Unit := ()) : Array (Array Nat) := e4f7Gens.map tvCols

@[expose] def e4f7Syn0 (_ : Unit := ()) : Array Nat := (mf7SpanData (tvCols 0)).syn

@[expose] def e4f7Root (_ : Unit := ()) : Nat :=
  let S := e4f7Syn0 ()
  ((List.range 75735).find? fun i => mf7Ap S (wt i) == 0).getD 0

@[expose] def e4f7Tree (_ : Unit := ()) : Array Nat × Array Nat :=
  let G := e4f7GenCols ()
  let S := e4f7Syn0 ()
  e4f7Bfs 75735 G.size (fun g u =>
    let v := wtIdx (mf7Ap G[g]! (wt u))
    if v < 75735 && mf7Ap S (wt v) == 0 then v else 75735) (e4f7Root ())

@[expose] def e4f7Word (T : Array Nat × Array Nat) (Gs : Array Nat) (i : Nat) : List Nat :=
  (e4f7TreeWord T.1 T.2 2000 i).map fun g => Gs[g]!

@[expose] def e4f7ApplyWord : List Nat → Nat → Nat
  | [], c => c
  | r :: w, c => mf7Ap (tvCols r) (e4f7ApplyWord w c)

@[expose] def e4f7ChkWord (_ : Unit := ()) : Bool :=
  let A := tvCols 0
  let Gs := e4f7Gens
  let S := e4f7Syn0 ()
  let T := e4f7Tree ()
  let r0 := e4f7Root ()
  decide (Gs.size ≤ 30) && Gs.all (fun r => decide (r < 365211) && mf7Commute A (tvCols r)) &&
  decide (r0 < 75735) && mf7Ap S (wt r0) == 0 &&
  mf7Count 75735 (fun i => mf7Ap S (wt i) == 0) == 135 &&
  mf7All 75735 fun i => mf7Ap S (wt i) != 0 ||
    (let w := e4f7Word T Gs i
     w.all (fun r => decide (r < 365211) && mf7Commute A (tvCols r)) &&
       e4f7ApplyWord w (wt r0) == wt i)

def e4f7FixIdx : Nat := 71

def e4f7FixPre : Nat := 39

@[expose] def e4f7ChkPlane (_ : Unit := ()) : Bool :=
  let A := tvCols 0
  let B := tvCols mf7Reps[4]!
  let Dl := mf7SpanData B
  decide (e4f7FixIdx < 75735) && decide (e4f7FixPre < 75735) &&
  (mf7Ap A (wt e4f7FixPre) ^^^ wt e4f7FixPre == wt e4f7FixIdx) &&
  mf7Ap B (wt e4f7FixIdx) == wt e4f7FixIdx && mf7Ap Dl.syn (wt e4f7FixIdx) != 0

end CFSG.SmithD6

module

public import CFSG.Blueprint.ChevalleyRootsInputs

public section

namespace CFSG.SmithE8M

open CFSG.Blueprint.Chevalley

@[expose] def e8mRoot (k : ℕ) : Fin (Tag.rank .E7) → ℤ := (Tag.rootCertificate .E7).root k

@[expose] def e8mRootArr (_ : Unit := ()) : Array (Fin (Tag.rank .E7) → ℤ) :=
  (Array.range 126).map (Tag.rootCertificate .E7).root

@[expose] def e8mConfA (A : Array (Fin (Tag.rank .E7) → ℤ)) (a b : ℕ) : Bool :=
  let s : Fin (Tag.rank .E7) → ℤ := fun i => A[a]! i + A[b]! i
  (List.range 126).any fun m => A[m]! == s

@[expose] def e8mIsPos (k : ℕ) : Bool := decide (0 < height (e8mRoot k))

@[expose] def e8mPos (_ : Unit := ()) : List ℕ := (List.range 126).filter e8mIsPos

@[expose] def e8mIsRA (k : ℕ) : Bool := decide (e8mRoot k ⟨6, by decide⟩ = 1)

@[expose] def e8mConfTab (A : Array (Fin (Tag.rank .E7) → ℤ)) : Array (Array Bool) :=
  (Array.range 126).map fun a => (Array.range 126).map fun b => e8mConfA A a b

@[expose] def e8mCf (T : Array (Array Bool)) (a b : ℕ) : Bool := (T[a]!)[b]!

@[expose] def e8mPick (cf : ℕ → ℕ → Bool) (P : List ℕ) : ℕ × ℕ :=
  P.foldl (fun best v => let d := (P.filter (cf v)).length; if best.2 < d then (v, d) else best)
    (0, 0)

@[expose] def e8mNoIndep (cf : ℕ → ℕ → Bool) : ℕ → List ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, P, k =>
    if k = 0 then false
    else if P.length < k then true
    else if (e8mPick cf P).2 = 0 then false
    else e8mNoIndep cf fuel (P.erase (e8mPick cf P).1) k &&
      e8mNoIndep cf fuel (P.filter fun u => u != (e8mPick cf P).1 && !cf (e8mPick cf P).1 u) (k - 1)

@[expose] def e8mTabOK (_ : Unit := ()) : Bool :=
  let A := e8mRootArr ()
  let T := e8mConfTab A
  (List.range 126).all (fun k => A[k]! == e8mRoot k) &&
    (List.range 126).all fun a => (List.range 126).all fun b => e8mCf T a b == e8mConfA A a b

@[expose] def e8mAbelCheck (_ : Unit := ()) : Bool :=
  let T := e8mConfTab (e8mRootArr ())
  let cf := e8mCf T
  let P := e8mPos ()
  e8mNoIndep cf 1000 P 28 &&
    (P.filter fun v => !e8mIsRA v).all fun v =>
      e8mNoIndep cf 1000 (P.filter fun u => u != v && !cf v u) 26

@[expose] def e8mRACheck (_ : Unit := ()) : Bool :=
  let A := e8mRootArr ()
  let RA := (List.range 126).filter e8mIsRA
  RA.length == 27 && RA.all e8mIsPos && RA.all fun a => RA.all fun b => !e8mConfA A a b

end CFSG.SmithE8M

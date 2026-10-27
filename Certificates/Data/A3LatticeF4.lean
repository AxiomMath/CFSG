module

public import Init

public section

namespace Certificates.A3LatticeF4

set_option compiler.extract_closed false

@[expose] def cartan : Array Int := #[2, -1, 0, 0, -1, 2, -1, 0, 0, -2, 2, -1, 0, 0, -1, 2]

@[expose] def symm : Array Int := #[4, -2, 0, 0, -2, 4, -2, 0, 0, -2, 2, -1, 0, 0, -1, 2]

@[expose] def rank : Nat := 4

@[expose] def reflect (i : Nat) (v : Array Int) : Array Int :=
  let k := (List.range rank).foldl (fun s j => s + cartan[rank * i + j]! * v[j]!) 0
  v.set! i (v[i]! - k)

@[expose] def basisVec (i : Nat) : Array Int := (Array.replicate rank (0 : Int)).set! i 1

@[expose] def addRoots (rs : List (Array Int)) : List (Array Int) :=
  (List.range rank).foldl (fun acc i =>
    rs.foldl (fun acc g => let h := reflect i g; if acc.contains h then acc else acc ++ [h]) acc) rs

@[expose] def rootsOf (_ : Unit := ()) : List (Array Int) :=
  (List.range 12).foldl (fun rs _ => addRoots rs) ((List.range rank).map basisVec)

@[expose] def form (u v : Array Int) : Int :=
  (List.range rank).foldl (fun s i =>
    s + u[i]! * (List.range rank).foldl (fun t j => t + symm[rank * i + j]! * v[j]!) 0) 0

@[expose] def pair3 (g : Array Int) (c : Array Nat) : Int :=
  ((List.range rank).foldl (fun s j => s + g[j]! * Int.ofNat c[j]!) 0) % 3

@[expose] def vecs : List (Array Nat) :=
  (List.range (3 ^ rank)).map fun m => Array.ofFn (n := rank) fun i => m / 3 ^ i.val % 3

@[expose] def comboZero (s t : Nat) (c₁ c₂ : Array Nat) : Bool :=
  (List.range rank).all fun j => (s * c₁[j]! + t * c₂[j]!) % 3 == 0

@[expose] def indep (c₁ c₂ : Array Nat) : Bool :=
  (List.range 3).all fun s => (List.range 3).all fun t =>
    (s == 0 && t == 0) || !comboZero s t c₁ c₂

@[expose] def comp (ks : List (Array Int)) (seed : Array Int) : List (Array Int) :=
  (List.range ks.length).foldl (fun cs _ =>
    ks.foldl (fun cs k =>
      if cs.contains k then cs
      else if cs.any (fun c => form c k != 0) then cs ++ [k] else cs) cs) [seed]

@[expose] def adjClosed (ks cs : List (Array Int)) : Bool :=
  cs.all fun c => ks.all fun k => form c k == 0 || cs.contains k

@[expose] def rootsClosed (rs : List (Array Int)) : Bool :=
  (List.range rank).all (fun i => rs.contains (basisVec i)) &&
    rs.all fun r => (List.range rank).all fun i => rs.contains (reflect i r)

@[expose] def mainCheck (rs : List (Array Int)) : Bool :=
  vecs.all fun c₁ => vecs.all fun c₂ =>
    !indep c₁ c₂ ||
    (let ks := rs.filter fun g => pair3 g c₁ == 0 && pair3 g c₂ == 0
     ks.all fun m => let cs := comp ks m; adjClosed ks cs && cs.length != 12)

@[expose] def verifyWith (rs : List (Array Int)) : Bool := rootsClosed rs && mainCheck rs

@[expose] def check (_ : Unit := ()) : Bool := verifyWith (rootsOf ())

end Certificates.A3LatticeF4

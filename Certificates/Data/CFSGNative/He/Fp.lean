module

public section

namespace CFSG.Sporadic.He.Native

@[inline, expose] def wsChar (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.toNat == 11 || c.toNat == 12

@[expose] def decodeEntries (s : String) : List Nat :=
  let body := (s.toList.dropWhile (· != '\n')).drop 1
  (body.filter fun c => !wsChar c).map fun c =>
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

@[expose] def rowsOf (p d : Nat) (s : String) : Array (Array Nat) :=
  let e := (decodeEntries s).toArray
  Array.ofFn (n := d) fun i => Array.ofFn (n := d) fun j => (e[i.val * d + j.val]?.getD 0) % p

@[expose] def dot (p d : Nat) (r v : Array Nat) : Nat :=
  (Nat.fold d (fun j _ acc => acc + r[j]! * v[j]!) 0) % p

@[expose] def mulVec (p d : Nat) (M : Array (Array Nat)) (v : Array Nat) : Array Nat :=
  Array.ofFn (n := d) fun i => dot p d M[i.val]! v

@[expose] def col (d : Nat) (Y : Array (Array Nat)) (k : Nat) : Array Nat :=
  Array.ofFn (n := d) fun j => Y[j.val]![k]!

@[expose] def mulM (p d : Nat) (X Y : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := d) fun i => Array.ofFn (n := d) fun k => dot p d X[i.val]! (col d Y k.val)

@[expose] def idM (d : Nat) : Array (Array Nat) :=
  Array.ofFn (n := d) fun i => Array.ofFn (n := d) fun j => if i.val = j.val then 1 else 0

@[expose] def powM (p d : Nat) (M : Array (Array Nat)) : Nat → Array (Array Nat)
  | 0 => idM d
  | e + 1 => mulM p d (powM p d M e) M

@[expose] def canonV (p d : Nat) (v : Array Nat) : Bool := v.size == d && v.all (· < p)

@[expose] def colsMat (d : Nat) (vs : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := d) fun i => Array.ofFn (n := d) fun t => vs[t.val]![i.val]!

@[expose] def invM (p d : Nat) (X : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let mut A : Array (Array Nat) := Array.ofFn (n := d) fun i =>
    Array.ofFn (n := 2 * d) fun j =>
      if j.val < d then X[i.val]![j.val]! % p else if j.val - d = i.val then 1 else 0
  for c in [0:d] do
    let mut piv := d
    for r in [c:d] do
      if piv == d && A[r]![c]! % p != 0 then piv := r
    if piv < d then
      let rowP := A[piv]!
      A := (A.set! piv A[c]!).set! c rowP
      let iv := A[c]![c]! ^ (p - 2) % p
      A := A.set! c (A[c]!.map fun x => x * iv % p)
      for r in [0:d] do
        if r != c then
          let f := A[r]![c]!
          if f != 0 then
            let rc := A[c]!
            let rr := A[r]!
            A := A.set! r (Array.ofFn (n := 2 * d) fun j => (rr[j.val]! + (p - f) * rc[j.val]!) % p)
  return A.map fun row => row.extract d (2 * d)

end CFSG.Sporadic.He.Native

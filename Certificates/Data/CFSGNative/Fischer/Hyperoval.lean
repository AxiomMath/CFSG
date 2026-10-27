module

public import Certificates.Data.CFSGNative.Fischer.Polar

public section

namespace CFSG.Fischer.Native

open CFSG.F4.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

abbrev Flags := Array Bool

@[expose] def filterRange (p : Nat → Bool) : Nat → List Nat → List Nat
  | 0, acc => acc
  | n + 1, acc => filterRange p n (if p n then n :: acc else acc)

@[inline, expose] def anyIn (n : Nat) (p : Nat → Bool) : Bool := !allIn 0 n fun i => !p i

@[expose] def perpTab (_ : Unit) : Array Flags :=
  Array.ofFn (n := 693) fun x =>
    let T := tvTabs[x.val]!
    Array.ofFn (n := 693) fun y => ap T y.val == y.val

@[expose] def perpList (P : Array Flags) (x : Nat) : Array Nat :=
  let r := P[x]!
  (filterRange (fun y => r[y]!) 693 []).toArray

@[noinline, expose] def perpLists (P : Array Flags) : Array (Array Nat) :=
  Array.ofFn (n := 693) fun x => perpList P x.val

@[expose] def members (F : Flags) : List Nat := filterRange (fun p => F[p]!) 693 []

@[expose] def lineC (x y : Nat) : Array Nat :=
  let cx := uPts[x]!
  let cy := uPts[y]!
  #[x, y, uPos[normC (cx ^^^ cy)]!, uPos[normC (cx ^^^ scaleC 2 cy)]!,
    uPos[normC (cx ^^^ scaleC 3 cy)]!]

@[expose] def normTab (_ : Unit) : Array Nat := Array.ofFn (n := 4096) fun c => normC c.val

@[expose] def scaleTab (a : Nat) : Array Nat := Array.ofFn (n := 4096) fun c => scaleC a c.val

@[inline, expose] def lineF (NT S2 S3 : Array Nat) (x y : Nat) : Array Nat :=
  let cx := uPts[x]!
  let cy := uPts[y]!
  #[x, y, uPos[NT[cx ^^^ cy]!]!, uPos[NT[cx ^^^ S2[cy]!]!]!, uPos[NT[cx ^^^ S3[cy]!]!]!]

@[noinline, expose] def lineTabOf (P : Array Flags) (NT S2 S3 : Array Nat) : Array (Array Nat) :=
  Array.ofFn (n := 693 * 693) fun k =>
    if P[k.val / 693]![k.val % 693]! then lineF NT S2 S3 (k.val / 693) (k.val % 693) else #[]

@[expose] def lineTab (P : Array Flags) : Array (Array Nat) :=
  lineTabOf P (normTab ()) (scaleTab 2) (scaleTab 3)

@[expose] def distinct5 (L : Array Nat) : Bool :=
  L.size == 5 && allIn 0 5 fun a => allIn 0 5 fun b => a == b || L[a]! != L[b]!

@[expose] def imgFlags (Ti : Table) (F : Flags) : Flags :=
  Array.ofFn (n := 693) fun q => F[ap Ti q.val]!

@[expose] def nzC (c : Nat) : Nat :=
  (if coord c 0 == 0 then 0 else 1) + (if coord c 1 == 0 then 0 else 1) +
    (if coord c 2 == 0 then 0 else 1) + (if coord c 3 == 0 then 0 else 1) +
    (if coord c 4 == 0 then 0 else 1) + (if coord c 5 == 0 then 0 else 1)

@[expose] def prodCoordC (c : Nat) : Nat :=
  f4mul (f4mul (f4mul (f4mul (f4mul (coord c 0) (coord c 1)) (coord c 2)) (coord c 3))
    (coord c 4)) (coord c 5)

@[expose] def rootFlags (c : Nat) : Flags :=
  Array.ofFn (n := 693) fun p =>
    let v := uPts[p.val]!
    nzC v == 2 || (nzC v == 6 && prodCoordC v == c)

@[noinline, expose] def linesOK (P : Array Flags) (pl : Array (Array Nat))
    (LT : Array (Array Nat)) : Bool :=
  allIn 0 693 fun x =>
    let px := P[x]!
    let plx := pl[x]!
    allIn 0 693 fun y => !(decide (x < y) && px[y]!) ||
      (let L := LT[x * 693 + y]!
       let N := plx.filter fun w => P[w]![y]!
       L.all (· < 693) && distinct5 L &&
         allIn 0 693 fun z => let pz := P[z]!; L.contains z == N.all (pz[·]!))

@[noinline, expose] def lineList (P : Array Flags) (LT : Array (Array Nat)) :
    Array (Array Nat) := Id.run do
  let mut out : Array (Array Nat) := #[]
  for x in [0:693] do
    for y in [x + 1:693] do
      if P[x]![y]! then
        let L := LT[x * 693 + y]!.qsort (· < ·)
        if L[0]! == x && L[1]! == y then out := out.push L
  return out

@[noinline, expose] def lineIdx (L : Array (Array Nat)) : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate (693 * 693) L.size
  for i in [0:L.size] do
    let l := L[i]!
    for a in [0:5] do
      for b in [0:5] do
        if a != b then r := r.set! (l[a]! * 693 + l[b]!) i
  return r

@[noinline, expose] def lineListOK (P : Array Flags) (LT : Array (Array Nat))
    (L : Array (Array Nat)) (I : Array Nat) : Bool :=
  L.size == 6237 &&
  allIn 0 693 (fun p => ((List.range 6237).filter fun i => L[i]!.contains p).length == 45) &&
  allIn 0 6237 (fun i =>
    let l := L[i]!
    l.size == 5 && l.all (· < 693) && l[0]! != l[1]! && P[l[0]!]![l[1]!]! &&
      (let m := LT[l[0]! * 693 + l[1]!]!; l.all (m.contains ·) && m.all (l.contains ·)) &&
      allIn 0 5 fun a => allIn 0 5 fun b => a == b || I[l[a]! * 693 + l[b]!]! == i) &&
  allIn 0 693 fun x =>
    let px := P[x]!
    allIn 0 693 fun y => x == y || !px[y]! ||
      (let i := I[x * 693 + y]!
       i < 6237 &&
         (let m := LT[x * 693 + y]!; let l := L[i]!; m.all (l.contains ·) && l.all (m.contains ·)))

@[noinline, expose] def twinsOK (P : Array Flags) (pl : Array (Array Nat))
    (LT : Array (Array Nat)) : Bool :=
  let D := pl[0]!
  D.all fun x => x == 0 ||
    (let L := LT[x]!
     let px := P[x]!
     D.all fun y => y == 0 || y == x ||
       (let py := P[y]!
        (D.all fun w => w == 0 || px[w]! == py[w]!) == L.contains y))

@[noinline, expose] def perpPerpOK (P : Array Flags) (pl : Array (Array Nat))
    (LT : Array (Array Nat)) : Bool :=
  let D := pl[0]!
  allIn 0 693 fun q => P[0]![q]! ||
    (let N := D.filter fun w => P[w]![q]!
     N.size == 45 &&
       N.any (fun a => N.any fun b => a != b && P[a]![b]! &&
         LT[a * 693 + b]!.any fun c => c != a && c != b && N.contains c) &&
       N.all (fun a => N.all fun b =>
         a == b || !P[a]![b]! || N.any fun w => P[w]![a]! != P[w]![b]!) &&
       allIn 0 693 fun q' => P[0]![q']! || !(D.all fun w => P[w]![q]! == P[w]![q']!) ||
         q' == q || q' == ap tvTabs[0]! q)

@[noinline, expose] def polarLinesChecks (P : Array Flags) (LT : Array (Array Nat)) : Bool :=
  let pl := perpLists P
  let L := lineList P LT
  allIn 0 693 (fun p => pl[p]!.size == 181) && linesOK P pl LT &&
    lineListOK P LT L (lineIdx L) && twinsOK P pl LT && perpPerpOK P pl LT

@[expose] def polarLinesCertificate (_ : Unit) : Bool :=
  let P := perpTab ()
  polarLinesChecks P (lineTab P)

@[expose] def deltaC (c : Nat) : Nat := c / 4 * 4 + f4mul 2 (c % 4)

@[expose] def deltaTab (_ : Unit) : Table :=
  Array.ofFn (n := 693) fun k => UInt32.ofNat uPos[normC (deltaC uPts[k.val]!)]!

@[noinline, expose] def deltaTabOK (P : Array Flags) (D : Table) : Bool :=
  let Di := invT 693 D
  invOK 693 D Di &&
    allIn 0 693 (fun a => ap D a < 693 &&
      (let pa := P[a]!; let pda := P[ap D a]!; allIn 0 693 fun b => pda[ap D b]! == pa[b]!)) &&
    allIn 0 693 (fun p => let T := tvTabs[p]!; let T' := tvTabs[ap D p]!;
      allIn 0 693 fun q => ap D (ap T q) == ap T' (ap D q)) &&
    rootFlags 2 == imgFlags Di (rootFlags 1) && rootFlags 3 == imgFlags Di (rootFlags 2) &&
    rootFlags 1 == imgFlags Di (rootFlags 3)

@[expose] def deltaCertificate (_ : Unit) : Bool :=
  deltaTabOK (perpTab ()) (deltaTab ())

end CFSG.Fischer.Native

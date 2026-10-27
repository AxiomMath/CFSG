module

public import Certificates.Data.CFSGNative.Fischer.HyperovalSearch

public section

namespace CFSG.Fischer.Native

open CFSG.F4.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[noinline, expose] def xiImg (H : Array Flags) (ix : Std.HashMap (Array UInt64) Nat) :
    Array (Array Nat) :=
  Array.ofFn (n := 1408) fun k =>
    let S := H[k.val]!
    let M := members S
    Array.ofFn (n := 693) fun f =>
      if S[f.val]! then k.val else findIn ix 4224 (packImg tvTabs[f.val]! M)

@[noinline, expose] def xiInv (H : Array Flags) (Im : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := 1408) fun k => Id.run do
    let S := H[k.val]!
    let row := Im[k.val]!
    let mut r : Array Nat := Array.replicate 1408 693
    for f in [0:693] do
      if !S[f]! then r := r.set! row[f]! f
    return r

@[noinline, expose] def xiAdj (Iv : Array (Array Nat)) : Array Flags :=
  Array.ofFn (n := 1408) fun k => Iv[k.val]!.map (· != 693)

@[noinline, expose] def xiImgOK (H : Array Flags) (Im Iv : Array (Array Nat)) : Bool :=
  allIn 0 1408 fun k =>
    let S := H[k]!
    let M := members S
    let row := Im[k]!
    let irow := Iv[k]!
    irow.size == 1408 && allIn 0 693 (fun f => S[f]! ||
      (let i := row[f]!
       i < 1408 && i != k && irow[i]! == f && (let T := tvTabs[f]!; let Si := H[i]!;
         M.all fun p => Si[ap T p]!))) &&
    allIn 0 1408 fun i => irow[i]! == 693 ||
      (let f := irow[i]!; f < 693 && !S[f]! && row[f]! == i)

@[noinline, expose] def xiInterOK (H : Array Flags) (A : Array Flags) : Bool :=
  let M := members H[0]!
  let a0 := A[0]!
  allIn 1 1408 fun i =>
    let Si := H[i]!
    let c := (M.filter (Si[·]!)).length
    if a0[i]! then c == 30 else c == 18

@[noinline, expose] def perpCountOK (P : Array Flags) (R : Flags) : Bool :=
  let M := members R
  allIn 0 693 fun f => R[f]! || (let r := P[f]!; (M.filter (r[·]!)).length == 30)

@[noinline, expose] def xiDiamOK (A : Array Flags) : Bool :=
  let a0 := A[0]!
  allIn 1 1408 fun v => a0[v]! ||
    ((anyIn 1408 fun x => a0[x]! && A[x]![v]!) &&
      allIn 1 1408 fun w => a0[w]! || !A[v]![w]! ||
        anyIn 1408 fun x => a0[x]! && A[x]![v]! && A[x]![w]!)

@[expose] def muTree (A : Array Flags) (v : Nat) : Array Nat × Array Nat × Array Nat := Id.run do
  let a0 := A[0]!
  let mu := (filterRange (fun x => a0[x]! && A[x]![v]!) 1408 []).toArray
  let mut pos : Array Nat := Array.replicate 1408 1408
  let mut pts : Array Nat := #[]
  let mut par : Array Nat := #[]
  if 0 < mu.size then
    pts := #[mu[0]!]
    par := #[0]
    pos := pos.set! mu[0]! 0
  for h in [0:1408] do
    if h < pts.size then
      let ax := A[pts[h]!]!
      for y in mu do
        if ax[y]! && pos[y]! == 1408 then
          pos := pos.set! y pts.size
          pts := pts.push y
          par := par.push h
    else break
  return (pts, par, pos)

@[expose] def muTreeOK (A : Array Flags) (v : Nat) (t : Array Nat × Array Nat × Array Nat) :
    Bool :=
  let a0 := A[0]!
  let pts := t.1
  let par := t.2.1
  let pos := t.2.2
  0 < pts.size && par.size == pts.size &&
    allIn 0 pts.size (fun i =>
      let x := pts[i]!
      x < 1408 && a0[x]! && A[x]![v]! && (i == 0 || (par[i]! < i && A[pts[par[i]!]!]![x]!))) &&
    allIn 0 1408 fun x => !(a0[x]! && A[x]![v]!) || (pos[x]! < pts.size && pts[pos[x]!]! == x)

@[noinline, expose] def xiMuOK (A : Array Flags) : Bool :=
  let a0 := A[0]!
  allIn 1 1408 fun v => a0[v]! || muTreeOK A v (muTree A v)

@[noinline, expose] def xiChecks (P : Array Flags) (H : Array Flags) : Bool :=
  let ix := famIndex H
  let Im := xiImg H ix
  let Iv := xiInv H Im
  let A := xiAdj Iv
  H.size == 4224 && xiImgOK H Im Iv && xiInterOK H A && perpCountOK P (rootFlags 1) &&
    perpCountOK P (rootFlags 2) && perpCountOK P (rootFlags 3) && xiDiamOK A && xiMuOK A

@[expose] def xiCertificate (_ : Unit) : Bool :=
  xiChecks (perpTab ()) (hypSets 1 ++ hypSets 2 ++ hypSets 3)

end CFSG.Fischer.Native

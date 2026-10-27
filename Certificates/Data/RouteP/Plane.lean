module

public import Certificates.Data.CFSGNative.Th.Orbit

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def planeList : List Nat :=
  [0, 1479, 99705, 867342, 105048, 96771, 11853, 18126, 894828, 102060, 50475, 14964, 94761,
    118191, 114276, 46821, 35007, 50637, 4071, 1521, 4374, 114891, 115167, 95736]

@[expose] def planeAList : List Nat :=
  [19, 2, 1, 10, 18, 9, 11, 21, 17, 5, 3, 6, 22, 16, 15, 14, 13, 8, 4, 0, 23, 7, 12, 20]

@[expose] def planeBList : List Nat :=
  [21, 22, 2, 0, 18, 14, 5, 17, 8, 16, 10, 11, 4, 1, 6, 15, 23, 20, 12, 19, 7, 3, 13, 9]

@[expose] def planeArr : Array Nat := planeList.toArray

@[expose] def planeAArr : Array Nat := planeAList.toArray

@[expose] def planeBArr : Array Nat := planeBList.toArray

structure TripleTree where
  us : Array Nat
  vs : Array Nat
  ws : Array Nat
  par : Array Nat
  lab : Array Nat
  pos : Array Nat

@[expose] def tripleBFS (pa pb : Array Nat) : TripleTree := Id.run do
  let absent := 13824
  let mut pos : Array Nat := Array.replicate absent absent
  let mut us : Array Nat := #[0]
  let mut vs : Array Nat := #[1]
  let mut ws : Array Nat := #[2]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  pos := pos.set! 26 0
  for h in [0:absent] do
    if h < us.size then
      for l in [0:2] do
        let p := if l == 0 then pa else pb
        let u := p[us[h]!]!
        let v := p[vs[h]!]!
        let w := p[ws[h]!]!
        let c := 576 * u + 24 * v + w
        if pos[c]! == absent then
          pos := pos.set! c us.size
          us := us.push u
          vs := vs.push v
          ws := ws.push w
          par := par.push h
          lab := lab.push l
    else break
  return ⟨us, vs, ws, par, lab, pos⟩

@[inline, expose] def tripleEdge (p : Array Nat) (T : TripleTree) (k : Nat) : Bool :=
  T.us[k]! == p[T.us[T.par[k]!]!]! && T.vs[k]! == p[T.vs[T.par[k]!]!]! &&
    T.ws[k]! == p[T.ws[T.par[k]!]!]!

@[expose] def tripleOK (pa pb : Array Nat) (T : TripleTree) : Bool :=
  let m := T.us.size
  pa.size == 24 && pb.size == 24 && T.vs.size == m && T.ws.size == m && T.par.size == m &&
    T.lab.size == m && 0 < m && T.us[0]! == 0 && T.vs[0]! == 1 && T.ws[0]! == 2 &&
    allIn 1 m (fun k => decide (T.par[k]! < k) &&
      ((T.lab[k]! == 0 && tripleEdge pa T k) || (T.lab[k]! == 1 && tripleEdge pb T k))) &&
    allIn 0 24 (fun u => allIn 0 24 (fun v => allIn 0 24 (fun w =>
      u == v || u == w || v == w ||
        (let k := T.pos[576 * u + 24 * v + w]!
         decide (k < m) && T.us[k]! == u && T.vs[k]! == v && T.ws[k]! == w))))

@[expose] def tripleTree (_ : Unit := ()) : TripleTree := tripleBFS planeAArr planeBArr

@[expose] def tripleCheck (_ : Unit := ()) : Bool :=
  tripleOK planeAArr planeBArr (tripleTree ())

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

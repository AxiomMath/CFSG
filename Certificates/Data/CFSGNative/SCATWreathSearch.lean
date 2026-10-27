module

public import Certificates.Data.CFSGNative.SCATWreathCode

public section

namespace CFSG.SCATWreath

structure GD where
  n : Nat
  mul : Nat → Nat → Nat
  gens : Array Nat
  ginv : Array Nat
  ord : Array Nat
  inv : Array Nat
  dom : List Nat
  lab : Array Nat
  reps : Array Nat
  wit : Array Nat
  csz : Array Nat

@[expose] def mkGD (n : Nat) (mul : Nat → Nat → Nat) (gens : Array Nat) (full : Bool) : GD :=
  let ord := if full then ordTab n mul else #[]
  let inv := if full then invTab n mul ord else #[]
  let ginv := gens.map fun g => pw mul g (ordc mul g - 1)
  let dom := if full then List.range n else invols n mul
  let L := labelBFS n mul gens ginv dom
  { n := n, mul := mul, gens := gens, ginv := ginv, ord := ord, inv := inv, dom := dom,
    lab := L.1, reps := L.2.1, wit := L.2.2, csz := histo L.2.1.size L.1 dom }

@[expose] def GD.ok (D : GD) (full : Bool) : Bool :=
  (!full || invOK D.n D.mul D.inv) && labOK D.n D.mul D.gens D.ginv D.lab D.reps D.wit D.dom

@[expose] def GD.conj (D : GD) (d u : Nat) : Nat := D.mul (D.mul d u) D.inv[d]!

@[expose] def cnt (D : GD) (H : List Nat) (u : Nat) : Nat := cntC D.mul H u

@[expose] def isMin (D : GD) (S : List Nat) (u : Nat) : Bool := S.all fun d => u ≤ D.conj d u

@[expose] def candOK (D : GD) (H : List Nat) (img0 g0 w cw u : Nat) : Bool :=
  D.ord[u]! == D.ord[w]! && D.csz[D.lab[u]!]! == D.csz[D.lab[w]!]! &&
    D.ord[D.mul u img0]! == D.ord[D.mul w g0]! && cnt D H u == cw

@[expose] def pairOK (D : GD) (img0 g0 gi gj ui uj : Nat) : Bool :=
  D.ord[D.mul ui uj]! == D.ord[D.mul gi gj]! &&
    D.ord[D.mul D.inv[ui]! uj]! == D.ord[D.mul D.inv[gi]! gj]! &&
    D.ord[D.mul (D.mul ui img0) (D.mul uj img0)]! == D.ord[D.mul (D.mul gi g0) (D.mul gj g0)]!

@[expose] def spotOK (D : GD) (par gi G imgs : Array Nat) (zl : List Nat)
    (spots : List (Nat × Nat)) : Bool :=
  zl.all (fun z => fpath D.mul par gi imgs D.n z != 0) &&
    spots.all fun s => fpath D.mul par gi imgs D.n (D.mul G[s.2]! s.1) ==
      D.mul imgs[s.2]! (fpath D.mul par gi imgs D.n s.1)

@[expose] def cands (D : GD) (H Hx : List Nat) (img0 g0 w : Nat) : List Nat :=
  let cw := cnt D Hx w
  (List.range D.n).filter (candOK D H img0 g0 w cw)

@[expose] def search (D : GD) (par gi G : Array Nat) (img0 : Nat) (H Hx zl : List Nat)
    (spots : List (Nat × Nat)) : List (Nat × Nat × Nat) :=
  let g0 := G[0]!
  let g1 := G[1]!
  let g2 := G[2]!
  let g3 := G[3]!
  let c2 := cands D H Hx img0 g0 g2
  let c3 := cands D H Hx img0 g0 g3
  ((cands D H Hx img0 g0 g1).filter (isMin D H)).flatMap fun u1 =>
    let S1 := H.filter fun d => D.conj d u1 == u1
    (c2.filter fun u2 => isMin D S1 u2 && pairOK D img0 g0 g1 g2 u1 u2).flatMap fun u2 =>
      let S2 := S1.filter fun d => D.conj d u2 == u2
      (c3.filter fun u3 => isMin D S2 u3 && pairOK D img0 g0 g1 g3 u1 u3 &&
          pairOK D img0 g0 g2 g3 u2 u3 && spotOK D par gi G #[img0, u1, u2, u3] zl spots).map
        fun u3 => (u1, u2, u3)

@[expose] def centList (D : GD) (x : Nat) : List Nat :=
  (List.range D.n).filter fun c => D.mul c x == D.mul x c

@[expose] def zList (D : GD) (G : Array Nat) : List Nat :=
  (List.range D.n).filter fun z => z != 0 && D.mul z z == 0 && G.all fun g => D.mul g z == D.mul z g

@[expose] def spotList (n : Nat) : List (Nat × Nat) :=
  (List.range 8).map fun k => ((k * 2654435761 + 12345) % n, k % 4)

@[expose] def gOK (D : GD) (G F : Array Nat) (g : Nat) : Bool :=
  (List.range G.size).all (fun i => F[F[G[i]!]!]! == D.conj g G[i]!) && F[g]! == g

end CFSG.SCATWreath

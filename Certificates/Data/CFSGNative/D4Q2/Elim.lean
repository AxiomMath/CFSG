module

public import Certificates.Data.CFSGNative.D4Q2.Check

public section

set_option compiler.extract_closed false

namespace CFSG.ClassicalInvolution.PhanDn.D4Q2

@[expose] def occBN (s : Array Nat) (y : Nat) : Bool := (List.range s.size).any fun k => s[k]! == y

@[expose] def adjBN (nbr : Array (Array Nat)) (x y : Nat) : Bool :=
  x != y && (occBN nbr[x]! y || occBN nbr[y]! x)

@[expose] def listOKN (n : Nat) (nb : Array (Array Nat)) (par : Nat → Nat)
    (rk ap bp : Nat → Nat → Nat) (tri : Nat → Nat → Nat → Bool) (x k : Nat) : Bool :=
  let y := (nb[x]!)[k]!
  let z := (nb[x]!)[ap x k]!
  x == y || n ≤ y ||
    (rk x k == 0 && ((0 < y && par y == x) || (0 < x && par x == y))) ||
    (0 < rk x k && ap x k < (nb[x]!).size && z < n && x != z && z != y && rk x (ap x k) < rk x k &&
      ((bp x k < (nb[z]!).size && (nb[z]!)[bp x k]! == y && rk z (bp x k) < rk x k) ||
        (bp x k < (nb[y]!).size && (nb[y]!)[bp x k]! == z && rk y (bp x k) < rk x k)) &&
      tri x z y)

@[expose] def okN (n : Nat) (nb : Array (Array Nat)) (par dep : Nat → Nat)
    (rk ap bp : Nat → Nat → Nat) (tri : Nat → Nat → Nat → Bool) : Bool :=
  0 < n &&
    (List.range n).all (fun x => x == 0 ||
      (par x < n && dep (par x) < dep x && adjBN nb (par x) x)) &&
    (List.range n).all fun x => (List.range (nb[x]!).size).all fun k =>
      listOKN n nb par rk ap bp tri x k

structure ElimTabs where
  par : Array Nat
  dep : Array Nat
  rk : Array (Array Nat)
  ap : Array (Array Nat)
  bp : Array (Array Nat)

@[expose] def posIn (s : Array Nat) (y : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := s.size
  for _ in [0:64] do
    if lo < hi then
      let mid := (lo + hi) / 2
      if s[mid]! < y then lo := mid + 1 else hi := mid
  if lo < s.size && s[lo]! == y then lo else s.size

@[expose] def elimTabs (N : Array (Array Nat)) : ElimTabs := Id.run do
  let n := N.size
  let inf := n * n + 1
  let mut par := Array.replicate n 0
  let mut dep := Array.replicate n inf
  dep := dep.set! 0 0
  let mut bfs : Array Nat := #[0]
  let mut h := 0
  for _ in [0:n] do
    if h < bfs.size then
      let u := bfs[h]!
      h := h + 1
      for v in N[u]! do
        if dep[v]! == inf then
          dep := dep.set! v (dep[u]! + 1)
          par := par.set! v u
          bfs := bfs.push v
  let mut rk : Array (Array Nat) := N.map fun r => Array.replicate r.size inf
  let mut ap : Array (Array Nat) := N.map fun r => Array.replicate r.size 0
  let mut bp : Array (Array Nat) := N.map fun r => Array.replicate r.size 0
  let mut q : Array (Nat × Nat) := #[]
  for v in [1:n] do
    let u := par[v]!
    rk := rk.modify v (·.set! (posIn N[v]! u) 0)
    rk := rk.modify u (·.set! (posIn N[u]! v) 0)
    q := q.push (u, v)
  let mut qh := 0
  for _ in [0:n * n] do
    if qh < q.size then
      let (a, b) := q[qh]!
      qh := qh + 1
      let r := (rk[a]!)[posIn N[a]! b]!
      let Na := N[a]!
      let Nb := N[b]!
      let mut i := 0
      let mut j := 0
      for _ in [0:Na.size + Nb.size] do
        if i < Na.size && j < Nb.size then
          let wa := Na[i]!
          let wb := Nb[j]!
          if wa < wb then i := i + 1
          else if wb < wa then j := j + 1
          else
            let w := wa
            let ra := (rk[a]!)[i]!
            let rb := (rk[b]!)[j]!
            if ra != inf && rb == inf then
              let s := max r ra + 1
              let pwb := posIn N[w]! b
              rk := rk.modify b (·.set! j s)
              ap := ap.modify b (·.set! j (posIn Nb a))
              bp := bp.modify b (·.set! j i)
              rk := rk.modify w (·.set! pwb s)
              ap := ap.modify w (·.set! pwb (posIn N[w]! a))
              bp := bp.modify w (·.set! pwb (posIn Na b))
              q := q.push (b, w)
            else if rb != inf && ra == inf then
              let s := max r rb + 1
              let pwa := posIn N[w]! a
              rk := rk.modify a (·.set! i s)
              ap := ap.modify a (·.set! i (posIn Na b))
              bp := bp.modify a (·.set! i j)
              rk := rk.modify w (·.set! pwa s)
              ap := ap.modify w (·.set! pwa (posIn N[w]! b))
              bp := bp.modify w (·.set! pwa (posIn Nb a))
              q := q.push (a, w)
            i := i + 1
            j := j + 1
        else break
    else break
  return ⟨par, dep, rk, ap, bp⟩

@[noinline, expose] def checkWith (T : Tabs) : Bool :=
  let N := nbOf T
  let E := elimTabs N
  sizeCheck T && frameCheck T && distinctCheck T && cliqueCheck T && apartCheck T &&
    okN 6720 N (fun x => E.par[x]!) (fun x => E.dep[x]!) (fun x k => (E.rk[x]!)[k]!)
      (fun x k => (E.ap[x]!)[k]!) (fun x k => (E.bp[x]!)[k]!) (fun _ _ _ => true)

@[expose] def check (_ : Unit := ()) : Bool := checkWith (tabs ())

end CFSG.ClassicalInvolution.PhanDn.D4Q2

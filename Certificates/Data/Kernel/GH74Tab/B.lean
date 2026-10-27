module

public import Certificates.Data.Kernel.GH74Tab.Defs

public section

namespace CFSG.KC.GH74Tab

open CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def transB (n : ℕ) [NeZero n] (A N4 N8 : Nat) : Bool :=
  let t := mkTab n
  (List.finRange 64).all fun k =>
    decide (a0perm n * emb n (t.el.get k) * (a0perm n)⁻¹ = emb n (t.el.get (f64 (g6 A k)))) &&
    (t.nm.get k == 4) == bit N4 k.val && (t.nm.get k == 8) == bit N8 k.val

variable (D : Dat)

@[expose] def autFK (ψ : Nat) : Bool :=
  g6 ψ D.one == D.one &&
  (r64.all fun i => r64.all fun j => g6 ψ (mul D i j) == mul D (g6 ψ i) (g6 ψ j)) &&
  r64.foldl (fun m i => m ||| 1 <<< g6 ψ i) 0 == 2 ^ 64 - 1

@[expose] def certK (A N4 N8 a X0 V0 s ψ : Nat) : Bool :=
  g6 ψ D.x0 == D.x0 &&
  (r64.all fun i => g6 ψ (mul D (mul D s (g6 a i)) (g6 D.I s)) == g6 A (g6 ψ i)) &&
  r64.all fun i => !bit D.IV i || ((!bit X0 i || bit N4 (g6 ψ i)) && (!bit V0 i || bit N8 (g6 ψ i)))

@[expose] def bK (A N4 N8 : Nat) (Ψ : List Nat) (p w : Nat × Nat) : Bool :=
  let a := p.1
  let u := p.2
  let s := w.1
  let X0 := reachK D a 12 (1 <<< D.x0)
  let V0 := reachK D a 12 (1 <<< mul D D.x0 (g6 a D.x0))
  u < 64 && (r64.all fun i => !bit D.IV i || bit X0 i || bit V0 i) &&
  s < 64 && w.2 < Ψ.length && mul D (mul D s (g6 a s)) u == D.one &&
  certK D A N4 N8 a X0 V0 s (Ψ.getD w.2 0)

@[expose] def bOK (A N4 N8 : Nat) (Ψ : List Nat) (L W : List (Nat × Nat)) : Bool :=
  Ψ.all (autFK D) && L.length == W.length && (L.zip W).all fun q => bK D A N4 N8 Ψ q.1 q.2

end CFSG.KC.GH74Tab

end

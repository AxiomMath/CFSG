module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeDefs

public section

namespace CFSG.AGLEmbedding.R3

@[expose] def incK : List (Nat × Nat) → Bool
  | x :: y :: l => decide (x.1 < y.1) && incK (y :: l)
  | _ => true

@[expose] def wSum (sp : List (Nat × Nat)) (f : Nat → Int) : Int :=
  (sp.map fun e => (e.2 : Int) * f e.1).sum

@[expose] def blkI (n B J : Nat) (sp : List (Nat × Nat)) : List (Nat × Nat) :=
  sp.filter fun e => decide (B ≤ e.1 / n / n ∧ e.1 / n / n < B + J)

@[expose] def blkT (n Q : Nat) (sp : List (Nat × Nat)) : List (Nat × Nat) :=
  sp.filter fun e => decide (e.1 / n / n = Q)

@[expose] def altCell (p : Nat) (m : NMod) (n B : Nat) (R T : List (Nat × Nat))
    (t : Nat → Nat → Int) : Bool :=
  (List.range n).all fun a => (List.range n).all fun b =>
    (wSum R (fun k => (m.acts.getD (k / n / n - B) default).ent n a (k / n % n) *
        (m.acts.getD (k / n / n - B) default).ent n b (k % n) - kd a (k / n % n) * kd b (k % n)) +
      wSum T (fun k => kd a (k / n % n) * kd b (k % n) + kd a (k % n) * kd b (k / n % n)) -
      t a b) % (p : Int) == 0

@[expose] def altW (p : Nat) (m : NMod) (n J N N' : Nat) (sp spt : List (Nat × Nat))
    (tgt : Nat → Nat → Nat → Nat → Int) : Bool :=
  decide (m.basis.length = n) && decide (m.acts.length = J) && incK sp && incK spt &&
  sp.all (fun e => decide (e.1 < N)) && spt.all (fun e => decide (e.1 < N')) &&
  (List.range n).all fun a₀ => (List.range n).all fun b₀ =>
    altCell p m n ((a₀ * n + b₀) * J) (blkI n ((a₀ * n + b₀) * J) J sp)
      (blkT n (a₀ * n + b₀) spt) (tgt a₀ b₀)

end CFSG.AGLEmbedding.R3

end

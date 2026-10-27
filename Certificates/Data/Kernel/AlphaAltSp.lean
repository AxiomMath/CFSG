module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeDefs

public section

namespace CFSG.AGLEmbedding.R3

@[expose] def spRowOK (m : NMod) (n : Nat) (S : List (Nat × Nat × Nat)) : Bool :=
  decide S.Nodup && S.all fun q => decide (q.1 < m.acts.length) && decide (q.2.1 < n) &&
    decide (q.2.2 < n)

@[expose] def spCoef (m : NMod) (n : Nat) (S : List (Nat × Nat × Nat)) (a b : Nat) : Int :=
  (S.map fun q => (m.acts.getD q.1 default).ent n a q.2.1 * (m.acts.getD q.1 default).ent n b q.2.2 -
    kd a q.2.1 * kd b q.2.2).sum

@[expose] def altSp (p : Nat) (m : NMod) (n : Nat) (T : List (List (Nat × Nat × Nat)))
    (tgt : Nat → Nat → Nat → Nat → Int) : Bool :=
  decide (m.basis.length = n) &&
  (List.range n).all fun a₀ => (List.range n).all fun b₀ =>
    spRowOK m n (T.getD (n * a₀ + b₀) []) &&
    (List.range n).all fun a => (List.range n).all fun b =>
      (spCoef m n (T.getD (n * a₀ + b₀) []) a b - tgt a₀ b₀ a b) % (p : Int) == 0

end CFSG.AGLEmbedding.R3

end

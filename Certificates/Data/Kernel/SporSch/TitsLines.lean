module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] def lineFlags (N V : Nat) (kappa beta : Array Nat) : Array Nat :=
  ((((List.range N).foldl (fun acc j => acc.modify kappa[j]! fun l => l ++ [j])
    (Array.replicate V [])).toList.map fun l =>
      l.mergeSort fun a b => decide (beta[a]! ≤ beta[b]!)).flatten.toArray)

@[expose] noncomputable def lineFlagsK (N V wk K wb B wl LF : Nat) : Bool :=
  bAnd(Nat.beq N (Nat.mul (nat_lit 3) V),
    allN V (fun v => strictB (Nat.mul (nat_lit 3) v) (fun b =>
      strictB (pg wl (mask wl) LF b) (fun f0 =>
      strictB (pg wl (mask wl) LF (Nat.add b (nat_lit 1))) (fun f1 =>
      strictB (pg wl (mask wl) LF (Nat.add b (nat_lit 2))) (fun f2 =>
      bAnd(Nat.blt f0 N, bAnd(Nat.blt f1 N, bAnd(Nat.blt f2 N,
      bAnd(Nat.beq (pg wk (mask wk) K f0) v, bAnd(Nat.beq (pg wk (mask wk) K f1) v,
      bAnd(Nat.beq (pg wk (mask wk) K f2) v,
      bAnd(lexLtK (pg wb (mask wb) B f0) f0 (pg wb (mask wb) B f1) f1,
        lexLtK (pg wb (mask wb) B f1) f1 (pg wb (mask wb) B f2) f2)))))))))))))

@[expose] noncomputable def orderK (V : Nat) (f : Nat → Nat) (SO SOI w : Nat) : Bool :=
  bAnd(allN V (fun i => strictB (pg w (mask w) SO i) (fun s =>
      bAnd(Nat.blt s V, Nat.beq (pg w (mask w) SOI s) i))),
    allN (Nat.sub V (nat_lit 1)) (fun i =>
      Nat.blt (f (pg w (mask w) SO i)) (f (pg w (mask w) SO (Nat.succ i)))))

end CFSG.KS.SporSch

end

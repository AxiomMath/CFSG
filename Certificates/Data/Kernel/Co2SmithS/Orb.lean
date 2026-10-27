module

public import Certificates.Data.Kernel.Co2SmithS.Replay

public section

namespace CFSG.KC.Co2SmithS

@[expose] def orbRecK (stepK : Nat → Nat → Nat) (ngen N start : Nat) (T PA LA M S : Nat → Nat)
    (TB : Nat → Nat → Nat) (i : Nat) : Bool :=
  (List.range ngen).all (fun l => decide (TB i l < N) && Nat.beq (stepK l (T i)) (T (TB i l))) &&
    Nat.beq (M (i + 1)) (if i < M i then rowC PA LA TB ngen i (M i) else 0) &&
    decide (S i < N) && (!(decide (i + 1 < N)) || decide (T (S i) < T (S (i + 1)))) &&
    (if i = 0 then Nat.beq (T 0) start && Nat.beq (PA 0) 0 && Nat.beq (LA 0) 0 && Nat.beq (M 0) 1
      else decide (PA i < i) && decide (LA i < ngen) && Nat.beq (T i) (stepK (LA i) (T (PA i))))

end CFSG.KC.Co2SmithS

end

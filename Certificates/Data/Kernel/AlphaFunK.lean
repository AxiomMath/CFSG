module

public import Certificates.Data.Kernel.AlphaGrpK

public section

namespace CFSG.AGLEmbedding.R3

@[expose] def blkF (n J Q : Nat) (sp : List (Nat × Nat)) : List (Nat × Nat) :=
  sp.filter fun e => decide (e.1 / n / J = Q)

@[expose] def funCell (p : Nat) (m : NMod) (n J : Nat) (R : List (Nat × Nat)) (r₀ : Nat) : Bool :=
  (List.range n).all fun r =>
    (wSum R (fun k => (m.acts.getD (k / n % J) default).ent n r (k % n) - kd r (k % n)) -
      kd r r₀) % (p : Int) == 0

@[expose] def funW (p : Nat) (m : NMod) (n J N : Nat) (sp : List (Nat × Nat)) : Bool :=
  decide (m.basis.length = n) && decide (m.acts.length = J) && decide (0 < J) && incK sp &&
  sp.all (fun e => decide (e.1 < N)) &&
  (List.range n).all fun r₀ => funCell p m n J (blkF n J r₀ sp) r₀

end CFSG.AGLEmbedding.R3

end

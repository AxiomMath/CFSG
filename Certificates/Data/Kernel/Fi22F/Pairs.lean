module

public import Certificates.Data.Kernel.Fi22F.Walks

public section

namespace CFSG.KC.Fi22F.Walks

open CFSG.KC CFSG.KC.HOrb CFSG.Sporadic.Presentation.Fi22Exact

@[expose] noncomputable def pwOK (blk : Nat → Nat) (nf : Nat) (ps : List (Conj × Conj)) (Rs : List Nat)
    (k₀ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun pp _ ih k => andB (andB (andB (lt6 (pairWord pp)) (Nat.blt (pairWord pp).length (nat_lit 1024)))
      (walkTo blk nf (entW (pairWord pp)) (nat_lit 0) (List.getD Rs k (nat_lit 0)) (nat_lit 0)))
      (ih (Nat.succ k))) ps k₀

end CFSG.KC.Fi22F.Walks

end

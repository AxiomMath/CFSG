module

public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.F2Word

public section

namespace CFSG.KC.F2AlgRank

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W

@[expose] noncomputable def algK (d : Nat) (G : List Nat) (tree : List (Nat × Nat))
    (acc : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun acc => k acc)
    (fun e _ ih acc => Prod.rec (motive := fun _ => Bool) (fun o g =>
      strictB (mulW d (getL (nat_lit 0) G g) (getL (nat_lit 0) acc o)) fun M => ih (M :: acc)) e)
    tree acc

@[expose] noncomputable def selK (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun M _ ih m => Nat.xor nIf(bit m (nat_lit 0), M, nat_lit 0) (ih (Nat.shiftRight m (nat_lit 1))))
    L

@[expose] noncomputable def rk2K (d T t w r s : Nat) : Bool :=
  allN d fun i => Nat.beq (rowF d T i)
    (Nat.xor nIf(bit t i, r, nat_lit 0) nIf(bit w i, s, nat_lit 0))

@[expose] noncomputable def sepK (d : Nat) (G : List Nat) (tree : List (Nat × Nat))
    (masks S : List Nat) (F Dm t w : Nat) : Bool :=
  algK d G tree [idF d] fun L =>
    andB (allN (Nat.pred d) fun k =>
        rk2K d (selK L (getL (nat_lit 0) masks k)) t w (rowF d F k) (getL (nat_lit 0) S k))
      (andB (Nat.beq (mulW d Dm F) (idF d)) (Nat.beq (vmF d (trK d Dm) (pw2 (Nat.pred d))) w))

end CFSG.KC.F2AlgRank

end

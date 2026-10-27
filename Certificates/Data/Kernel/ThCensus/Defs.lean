module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.DceS

public section

namespace CFSG.KC.ThCensus

open CFSG.KC.Th CFSG.KC.Th.BigS

@[expose] noncomputable def seedsOK (RB : Nat → Nat) (SA SB : Nat) : Bool :=
  andB (Nat.beq (RB 1) SA) (Nat.beq (RB 2) SB)

@[expose] noncomputable def slpStart (Cs : List Nat) (i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 3)
    (fun j acc => Nat.add acc (Nat.land (Cs.getD j 0) (nat_lit 255))) i

@[expose] noncomputable def slpChunkOK (RB : Nat → Nat) (c rm ONE : Nat) (Cs : List Nat) (i : Nat) :
    Bool :=
  Nat.beq (runSlp RB c rm ONE [Cs.getD i 0] (slpStart Cs i)) (slpStart Cs (Nat.succ i))

@[expose] noncomputable def inLayout (rm v : Nat) : Bool := Nat.beq (Nat.land v rm) v

@[expose] noncomputable def blockOK (RB PTS : Nat → Nat) (rm PR n BL b off : Nat) (TC SC : List Nat) :
    Bool :=
  (fun fr to => (fun N => andB (inLayout rm (PTS off))
      (andB (baseFixed RB rm PR (PTS off) to n)
        (andB (Nat.beq (runTree RB (fun k => PTS (Nat.add off k)) rm PR fr to TC (nat_lit 2)) (Nat.succ N))
          (Nat.beq (DceS.sortedCount (DceS.runSorted (fun k => PTS (Nat.add off k)) (nat_lit 11) N SC (nat_lit 1)))
            N))))
    (Nat.pow (nat_lit 3) (Nat.sub to fr)))
  (bitsN BL (Nat.mul (nat_lit 10) b) (nat_lit 5)) (bitsN BL (Nat.add (Nat.mul (nat_lit 10) b) (nat_lit 5)) (nat_lit 5))

@[expose] noncomputable def tabRowOK (PTS : Nat → Nat) (rm P off m : Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun t _ ih j => andB (andB (Nat.blt t m) (andB (inLayout rm (PTS (Nat.add off j)))
        (Nat.beq (vecB rm (PTS (Nat.add off j)) P) (PTS (Nat.add off t))))) (ih (Nat.succ j))) l

@[expose] noncomputable def lenN {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ acc => Nat.succ acc) l

@[expose] noncomputable def tabOK (PTS : Nat → Nat) (rm P off m : Nat) (l : List Nat) : Bool :=
  andB (Nat.beq (lenN l) m) (tabRowOK PTS rm P off m l (nat_lit 0))

end CFSG.KC.ThCensus

end

module

public import Certificates.Data.Kernel.J4Run

public section

namespace CFSG.KJ4.R

open CFSG.KJ4 CFSG.KJ4.S CFSG.KC.Loop

@[expose] noncomputable def row11 (M : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight M (nat_lit 132)) (nat_lit 4095)) (nat_lit 2048)

@[expose] noncomputable def fixEnt (NF e : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Nat.blt (Nat.shiftRight (Nat.land (Nat.shiftRight e (nat_lit 16)) (nat_lit 65535)) (nat_lit 1)) NF)
    (Nat.blt (Nat.land (Nat.shiftRight e (nat_lit 32)) (nat_lit 65535)) NF)
    (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def fixRun (NF m C : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih C => letB C (fun C' => andB (fixEnt NF (Nat.land C' (nat_lit 18446744073709551615)))
      (ih (Nat.shiftRight C' (nat_lit 64))))) m C

@[expose] noncomputable def fixL (NF : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun C _ ih =>
    andB (fixRun NF (Nat.land C (nat_lit 4095)) (Nat.shiftRight C (nat_lit 12))) ih) l

@[expose] noncomputable def fixLs (NF : Nat) (Ls : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun L _ ih => andB (fixL NF L) ih) Ls

@[expose] noncomputable def fixEt (NF : Nat) (ET : Nat → Nat) (e : Nat) : Bool :=
  letB (ET e) (fun E => Bool.rec (motive := fun _ => Bool) true (Nat.blt (eA E) NF)
    (Nat.beq (eK E) (nat_lit 1)))

@[expose] noncomputable def fixDch (NF : Nat) (Ls : List ((Nat → Nat) × (Nat × (List Nat × Nat)))) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih =>
    andB (Prod.rec (motive := fun _ => Bool) (fun E r =>
      Prod.rec (motive := fun _ => Bool) (fun ne _ => allIn (nat_lit 0) ne (fixEt NF E)) r) c) ih) Ls

@[expose] noncomputable def j4Fix (k : KD) (FLs : List (List Nat)) : Bool :=
  andB (Nat.blt k.cv k.NF) (andB (row11 (letMat k.LET (nat_lit 0))) (andB (row11 k.W0)
  (andB (chkLin (letMat k.LET (nat_lit 2))) (andB (fixDch k.NF k.DCH) (fixLs k.NF FLs)))))

end CFSG.KJ4.R

end

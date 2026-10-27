module

public import Certificates.Data.Kernel.U38QK
public import Certificates.Data.Kernel.MonsterB.Co2Count

public section

namespace CFSG.KC.U38NoE81K

open CFSG.KC.Enum CFSG.KS CFSG.KC.Co2Mem

@[expose] noncomputable def comK (n w : Nat) (ps : List Nat) (x y : Nat) : Bool :=
  Nat.beq (PGrp.keyCK n w ps x y) (PGrp.keyCK n w ps y x)

@[expose] noncomputable def cenK (n w : Nat) (ps : List Nat) (T : Nat → Nat) (N u : Nat) : Nat :=
  strictN (T u) fun x => cntK N fun j => strictB (T j) fun y => comK n w ps x y

@[expose] noncomputable def cenOK (n w : Nat) (ps : List Nat) (T : Nat → Nat) (N u v : Nat) :
    Bool :=
  strictB (cenK n w ps T N u) fun c =>
    strictB (Nat.mod (Nat.div v (nat_lit 1024)) (nat_lit 1024)) fun j =>
      strictB (Nat.mod v (nat_lit 1024)) fun k =>
        bAnd(Nat.beq c (Nat.div v (nat_lit 1048576)),
          bIf(Nat.beq c (nat_lit 81),
            bAnd(Nat.blt j N, bAnd(Nat.blt k N, bAnd(comK n w ps (T u) (T j),
              bAnd(comK n w ps (T u) (T k), !(comK n w ps (T j) (T k)))))),
            true))

@[expose] noncomputable def bigK (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun v _ acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
      (Nat.ble (nat_lit 243) (Nat.div v (nat_lit 1048576))))) L

end CFSG.KC.U38NoE81K

end

module

public import Certificates.Data.Kernel.SporSch.MathieuBT

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.MOC

@[expose] noncomputable def zOrbK (n w m nr q Z : Nat) (RP OT : Nat → Nat) (d : ClsD) (k : Nat) :
    Bool :=
  bIf(Nat.blt k d.c, strictB (OT k) (fun o =>
    strictB (pg (nat_lit 16) (nat_lit 65535) o (nat_lit 1)) (fun j =>
    strictB (pg (nat_lit 16) (nat_lit 65535) o (nat_lit 2)) (fun e =>
    bAnd(Nat.blt j nr, bAnd(Nat.blt e q,
      bIf(Nat.beq e (nat_lit 0), Nat.beq (RP j) k,
        strictB (pg (nat_lit 16) (nat_lit 65535) o (nat_lit 0)) (fun p => bAnd(Nat.blt p d.c,
          strictB (OT p) (fun o' =>
            bAnd(Nat.beq (pg (nat_lit 16) (nat_lit 65535) o' (nat_lit 1)) j,
            bAnd(Nat.beq (Nat.succ (pg (nat_lit 16) (nat_lit 65535) o' (nat_lit 2))) e,
              Nat.beq (pcomp n w m Z (d.ST p)) (pcomp n w m (d.ST k) Z)))))))))))), true)

@[expose] noncomputable def zRepLtK (nr c : Nat) (RP : Nat → Nat) : Bool :=
  allN nr (fun j => Nat.blt (RP j) c)

@[expose] noncomputable def clsSub (d : ClsD) (nr : Nat) (RP : Nat → Nat) : ClsD :=
  ⟨d.R, nr, d.r, fun j => d.ST (RP j), d.IA, d.IB, d.PA, d.LB, d.DP⟩

end CFSG.KS.SporSch.MBT

end

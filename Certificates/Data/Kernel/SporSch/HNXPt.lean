module

public import Certificates.Data.Kernel.SporSch.HNXOrb
public import Certificates.Data.Kernel.SporSch.HNF5
public import CFSG.Certificates.Kernel.Local.HN.Lib
public import CFSG.Certificates.Kernel.Local.HN.X.Lib

public section

namespace CFSG.KC.LL.HNX

open CFSG.KC.Loop CFSG.KC.LL

@[expose] noncomputable def listA (T : Nat → Nat) (M FL c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft
      (Nat.land (getRec T (nat_lit 464) (fldW FL (Nat.mul (nat_lit 21) k) (nat_lit 21))) M)
      (Nat.mul (nat_lit 1729) k))) c

@[expose] noncomputable def ptsImg (T : Nat → Nat) (MS CM3 M G FL IL c : Nat) : Bool :=
  letB (mulC CM3 (listA T M FL c) G) (fun Y =>
    CFSG.KC.Enum.allN c (fun k => Nat.beq (fldW Y (Nat.mul (nat_lit 1729) k) (nat_lit 1729))
        (spread MS (fldW (getRec T (nat_lit 464) (fldW IL (Nat.mul (nat_lit 21) k) (nat_lit 21)))
          (nat_lit 0) (nat_lit 399)))))

@[expose] noncomputable def fixSum (T : Nat → Nat) (CM3 M G lo n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc (fun a => Nat.add a
      (fixLeaf T (nat_lit 464) CM3 M [G] (Nat.add lo i)
        (CFSG.KS.SporSch.hnxC (Nat.add lo i))))) n

@[expose] noncomputable def wordC (R : Nat → Nat) (cs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) CFSG.KD.OrdHN.ONE
    (fun c _ ih => CFSG.KC.LL.HN.mm (R c) ih) cs

@[expose] noncomputable def lanesEq (W : Nat) (Y : Nat → Nat) : Bool :=
  CFSG.KC.Enum.allN (nat_lit 133) (fun r => letB (fldW W (Nat.mul (nat_lit 1729) r) (nat_lit 1729))
    (fun w => letB (Y r) (fun y => CFSG.KC.Enum.allN (nat_lit 133) (fun c =>
      Nat.beq (fldW w (Nat.mul (nat_lit 13) c) (nat_lit 13)) (CFSG.KS.SporSch.lane5 y c)))))

end CFSG.KC.LL.HNX

end

module

public import Certificates.Data.Kernel.T75JM.L2K

public section

namespace CFSG.KC.N0K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75JM

@[expose] noncomputable def invAt (A T : Nat) : Bool :=
  (List.range 22).all fun x => Nat.beq (fdN 5 A (fdN 5 T (fdN 5 A (fdN 5 T x)))) x

@[expose] noncomputable def allW2 (ws : List (List Nat)) (g : Nat → List Nat → List Nat → Bool) :
    List (List Nat) → Nat → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Nat → Bool) (fun _ _ => true)
    (fun u _ ih rs i => g i u (List.headD rs []) && ih (List.tail rs) (Nat.succ i)) ws

@[expose] noncomputable def icOne (L : Int → Nat) (B0 A T c : Nat) : Bool :=
  conjAt (ak L (c / 16)) (tk L (c % 16)) B0 (pc A T)

@[expose] noncomputable def icE (L : Int → Nat) (B0 : Nat) (rs : List (List Nat)) : Bool :=
  allW2 a6Words (fun a u r => strictB (wordK 22 5 idn L (u.map a6Z)) fun A =>
    (List.range 16).all fun k => strictB (tk L k) fun T =>
      Nat.beq a 0 || !(invAt A T) || icOne L B0 A T (r.getD k 0)) rs (nat_lit 0)

@[expose] noncomputable def icK (L : Int → Nat) (rs : List (List Nat)) : Bool :=
  withL L fun L => strictB (pw L (bGen 0)) fun B0 => icE L B0 rs

end CFSG.KC.N0K

end

module

public import Certificates.Data.Kernel.Sp6Insp443.Cent
public import Certificates.Data.Kernel.KGC31P

public section

namespace CFSG.KS.Sp6I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Th.Native

@[expose] noncomputable def cellOK (n w c : Nat) (T : Table) : Bool :=
  bAnd(Nat.beq T.size n, bAnd(permOK n w (mask w) (Nat.mul n w) c (pinvS n w (mask w) c),
    tabPK n w (mask w) c T))

@[expose] noncomputable def rowOK (n w : Nat) : List Nat → List Table → Bool :=
  List.rec (motive := fun _ => List Table → Bool)
    (fun Ts => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Ts)
    (fun c _ ih Ts => List.rec (motive := fun _ => Bool) false
      (fun T Ts' _ => bAnd(cellOK n w c T, ih Ts')) Ts)

@[expose] noncomputable def gridOK (n w : Nat) : List (List Nat) → List (List Table) → Bool :=
  List.rec (motive := fun _ => List (List Table) → Bool)
    (fun Ts => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Ts)
    (fun c _ ih Ts => List.rec (motive := fun _ => Bool) false
      (fun T Ts' _ => bAnd(rowOK n w c T, ih Ts')) Ts)

end CFSG.KS.Sp6I

end

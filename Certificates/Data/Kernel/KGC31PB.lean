module

public import Certificates.Data.Kernel.KGC31P
public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.KGC31P

open CFSG.KC.Enum CFSG.KS

variable (n w : Nat)

@[expose] noncomputable def trPL (LR TR : Nat → Nat) (k : Nat) : List (List Nat) :=
  (List.range k).map fun i =>
    (List.range (CFSG.KS.Raw.rcnt (LR i))).map fun a => TR (CFSG.KS.Raw.roff n (n * w) (LR i) + a)

@[expose] noncomputable def pcountProducts (f : Nat → Bool) : List (List Nat) → Nat → Nat
  | [], g => if f g then 1 else 0
  | T :: Ts, g => T.foldl (fun c t => c + pcountProducts f Ts (pc n w g t)) 0

@[expose] noncomputable def pfilterProducts (f : Nat → Bool) :
    List (List Nat) → Nat → List Nat → List Nat
  | [], g, acc => if f g then g :: acc else acc
  | T :: Ts, g, acc => T.foldl (fun acc t => pfilterProducts f Ts (pc n w g t) acc) acc

@[expose] noncomputable def pcosetOK (b : Nat) (bs rs : List Nat) : Bool :=
  rs.length + 1 == 2 ^ bs.length &&
    (List.range rs.length).all fun m =>
      Nat.beq (pcj n w (rs.getD m (pidn n w)) (pinv n w (rs.getD m (pidn n w))) b)
        (pmask n w bs (m + 1))

@[expose] noncomputable def pcosetCount (cb rs : List Nat) (f : Nat → Bool) : Nat :=
  (rs.map fun r => cb.countP fun c => f (pc n w r c)).sum

end CFSG.KC.KGC31P

end

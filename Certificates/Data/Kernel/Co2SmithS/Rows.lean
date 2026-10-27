module

public import Certificates.Data.Kernel.Co2InvS
public import Certificates.Data.CFSGNative.Co2Smith.Sp6Pres

public section

namespace CFSG.KC.Co2SmithS

open CFSG.KC.Co2InvS CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def wK (f : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) IDP (fun k _ acc => mulV (f k) acc) w

@[expose] noncomputable def powV (M e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) IDP (fun _ acc => mulV acc M) e

@[expose] noncomputable def sp6CheckK (F : Nat → Nat) (a b : Nat) : Bool :=
  (List.range 8).all (fun i => Nat.beq (wK F [2 * i, 2 * i + 1]) IDP) &&
    (sp6Rels ()).all (fun r => Nat.beq (wK F (r.map sCode)) IDP) &&
    (List.finRange 8).all (fun i =>
      Nat.beq (wK F ((commWordsN (sp6Pairs i)).map sCode)) (wK F [2 * i.val])) &&
    Nat.beq (wK F ((sp6Wa ()).map sCode)) a && Nat.beq (wK F ((sp6Wb ()).map sCode)) b

end CFSG.KC.Co2SmithS

end

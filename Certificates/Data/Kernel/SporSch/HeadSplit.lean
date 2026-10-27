module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu

@[expose] noncomputable def headJ (n w m nw idn : Nat) (S SI : Nat → Nat) (kO : Nat)
    (D : List (List Int)) (nb BP j : Nat) : Bool :=
  bAnd(permOK n w m nw (S j) (SI j),
  bAnd(bIf(Nat.blt j kO, true,
    strictB (S j) (fun sj => bAnd(lettersK j (dword D kO j),
      Nat.beq sj (wordK n w m idn S SI (dword D kO j))))),
  bIf(allN nb (fun t => strictB (pg w m BP t) (fun b => Nat.beq (pg w m (S j) b) b)),
    Nat.beq (S j) idn, true)))

@[expose] noncomputable def headRest (n w m : Nat) (kS kO : Nat) (D : List (List Int)) (nb BP : Nat) :
    Bool :=
  bAnd(szOK n w, bAnd(Nat.blt kS (nat_lit 128), bAnd(Nat.ble kO kS,
  bAnd(Nat.beq (Nat.add (lenW D) kO) kS, allN nb (fun t => Nat.blt (pg w m BP t) n)))))

end CFSG.KS.SporSch

end

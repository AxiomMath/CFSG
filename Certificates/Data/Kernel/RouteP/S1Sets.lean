module

public import Certificates.Data.Kernel.RouteP.Geom
public import Certificates.Data.Kernel.RouteP.MonoW

public section

namespace CFSG.KC.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS

@[expose] noncomputable def subP (a b : Nat) : Bool := Nat.beq (Nat.land a b) a

@[expose] noncomputable def allL {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => andB (f a) ih) l

@[expose] noncomputable def s1CoverCore (NWP : Nat → Nat → Nat) (KAP KBP : Nat → Nat)
    (NWO : Nat → Nat → Nat) (KAO KBO : Nat → Nat) (ag tY : List Int) (y G0 A O : Nat) : Bool :=
  andB (ptOK NWP KAP KBP tY 1479 y)
    (andB (memP G0 y) (andB (notB (memP A y)) (andB (closedS NWO KAO KBO ag O)
      (andB (Nat.beq (Nat.land A O) 0) (andB (notB (memP A 1479)) (andB (notB (memP O 1479))
        (andB (subP A G0) (andB (subP O G0) (subP G0 (Nat.lor (single 1479) (Nat.lor A O)))))))))))

@[expose] noncomputable def s1CoverOK (NWP : Nat → Nat → Nat) (KAP KBP : Nat → Nat)
    (NWO : Nat → Nat → Nat) (KAO KBO : Nat → Nat) (zg ag tY : List Int) (y rO : Nat) : Bool :=
  letB (closeS NWP KAP KBP zg 33 (single 1479)) fun G0 =>
  letB (closeS NWO KAO KBO ag 10 (single 99705)) fun A =>
  letB (closeS NWO KAO KBO ag rO (single y)) fun O =>
  s1CoverCore NWP KAP KBP NWO KAO KBO ag tY y G0 A O

@[expose] noncomputable def s1HubsGo (NWO : Nat → Nat → Nat) (KAO KBO : Nat → Nat) (B2 A By : Nat)
    (fin : Nat → Bool) (hs : List (Nat × Nat × List Int)) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Bool) (fun _ U => fin U)
    (fun e _ ih prev U =>
      letB (imgW NWO KAO KBO e.2.2 B2) fun N =>
        andB (ptOK NWO KAO KBO e.2.2 99705 e.1)
          (andB (memP A e.1) (andB (memP By e.1)
            (andB (orB (Nat.beq prev.length 0)
                (andB (Nat.blt e.2.1 prev.length) (memP (prev.getD e.2.1 0) e.1)))
              (ih (prev ++ [N]) (Nat.lor U N))))))
    hs

@[expose] noncomputable def s1HubsOK (NWP : Nat → Nat → Nat) (KAP KBP : Nat → Nat)
    (NWO : Nat → Nat → Nat) (KAO KBO : Nat → Nat) (ag tY t2 : List Int) (w : Nat)
    (hs : List (Nat × Nat × List Int)) : Bool :=
  letB (closeS NWO KAO KBO ag 10 (single 99705)) fun A =>
  letB (imgW NWP KAP KBP tY A) fun By =>
  letB (imgW NWP KAP KBP t2 A) fun B2 =>
  letB (Nat.land A By) fun mu =>
  letB (Nat.xor By mu) fun D =>
  andB (ptOK NWP KAP KBP t2 1479 99705) (andB (memP A w) (andB (memP By w)
    (s1HubsGo NWO KAO KBO B2 A By
      (fun U => andB (subP mu (Nat.lor (single (hs.headD (0, 0, [])).1) U)) (subP D U)) hs [] 0)))

@[expose] noncomputable def s1StabOK (NWP : Nat → Nat → Nat) (KAP KBP : Nat → Nat)
    (NWO : Nat → Nat → Nat) (KAO KBO : Nat → Nat) (ag t2 : List Int) (ss : List (List Int))
    (c0 rC : Nat) : Bool :=
  letB (closeS NWO KAO KBO ag 10 (single 99705)) fun A =>
  letB (imgW NWP KAP KBP t2 A) fun B2 =>
  andB (ptOK NWP KAP KBP t2 1479 99705)
    (andB (allL ss fun s => ptOK NWO KAO KBO s 99705 99705)
      (subP (Nat.land A B2) (closeW NWO KAO KBO ss rC (single c0))))

end CFSG.KC.RouteP

end

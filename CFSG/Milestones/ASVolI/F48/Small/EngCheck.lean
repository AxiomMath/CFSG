module

public import CFSG.Quasithin.Recognition.CertPermList

public section

namespace CFSG.ASVolI

open CFSG.Quasithin

@[expose] def burnsideF48s_ev {G : Type*} [Group G] {m : ℕ} (h : Fin m → G)
    (w : List (Fin m × Bool)) : G :=
  (w.map fun l => cond l.2 (h l.1) (h l.1)⁻¹).prod

section Lists

variable {n : ℕ}

@[expose] def burnsideF48s_eLetL (LS LSi : List (List ℕ)) (l : Fin n × Bool) : List ℕ :=
  (if l.2 then LS else LSi).getD l.1 []

@[expose] def burnsideF48s_eEvL (N : ℕ) (LS LSi : List (List ℕ)) (w : List (Fin n × Bool)) :
    List ℕ :=
  w.foldl (fun acc l => compL acc (burnsideF48s_eLetL LS LSi l)) (List.range N)

@[expose] def burnsideF48s_eInvW (w : List (Fin n × Bool)) : List (Fin n × Bool) :=
  (w.map fun l => (l.1, !l.2)).reverse

@[expose] def burnsideF48s_eCandRel (m : ℕ) (u v w : List (Fin n × Bool)) :
    List (Fin n × Bool) :=
  (List.replicate m (u ++ v)).flatten ++ burnsideF48s_eInvW w

@[expose] def burnsideF48s_eWs (R1 R2 : List (List (Fin n × Bool))) (m : ℕ)
    (u v w : List (Fin n × Bool)) : List (List (Fin n × Bool)) :=
  R1 ++ R2 ++ [burnsideF48s_eCandRel m u v w]

end Lists

@[expose] def burnsideF48s_eNorm (KL : List (List ℕ)) (x : List ℕ) : Bool :=
  KL.all fun k => KL.any fun k' => compL x k == compL k' x

@[expose] def burnsideF48s_eCandOK (P1L P2L KL TL UL VL WL : List (List ℕ)) : Bool :=
  P1L.all fun x =>
    !burnsideF48s_eNorm KL x || !KL.contains (compL x x) || P2L.contains x ||
    P2L.all fun y =>
      !burnsideF48s_eNorm KL y || !KL.contains (compL y y) || P1L.contains y ||
      KL.all fun c => TL.any fun t => (List.range UL.length).any fun k =>
        compL t x == compL (UL.getD k []) t && compL t y == compL (VL.getD k []) t &&
          compL t c == compL (WL.getD k []) t

@[expose] def burnsideF48s_eClosed (L LS : List (List ℕ)) (gs : List ℕ) : Bool :=
  L.all fun x => gs.all fun g => L.contains (compL x (LS.getD g []))

@[expose] def burnsideF48s_eClosedW (L GW : List (List ℕ)) : Bool :=
  L.all fun x => GW.all fun g => L.contains (compL x g)

end CFSG.ASVolI

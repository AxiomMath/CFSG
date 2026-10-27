module

public import Certificates.Data.Kernel.CoreD2K.Check

public section

namespace CFSG.KS.CoreD2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 Certificates.CoreD2Perm

@[expose] def keepWs (keep : List Nat) : Nat → List (List Int) → List (List Int)
  | _, [] => []
  | j, w :: ws => (if keep.contains j then w else []) :: keepWs keep (j + 1) ws

structure CStep where
  tgt : Nat
  src : Nat
  j : Nat
  a : Nat
  b : Nat
deriving Inhabited

@[expose] noncomputable def repCK (n w : Nat) (V : VData) (GP GT GTI : Nat → Nat) (i : Nat) :
    Bool :=
  bAnd(Nat.blt i V.ys.length,
  bAnd(wordEqK n w (mask w) (pidn n w) GT GTI V.base.gWs.length (V.wAs.getD i []) (GP (nat_lit 0)),
  bAnd(wordEqK n w (mask w) (pidn n w) GT GTI V.base.gWs.length (V.wBs.getD i []) (GP (nat_lit 1)),
  bAnd(wordOK V i (V.wAs.getD i []), wordOK V i (V.wBs.getD i [])))))

@[expose] noncomputable def stepCK (n w : Nat) (V : VData) (EG GT : Nat → Nat) (s : CStep) : Bool :=
  strictB (EG (nat_lit 0)) (fun z =>
  bAnd(Nat.blt s.j V.base.gWs.length, bAnd(Nat.blt s.src V.ys.length,
  bAnd(Nat.blt s.tgt V.ys.length,
  bAnd(Nat.beq (pcomp n w (mask w) (GT s.j) z) (pcomp n w (mask w) z (GT s.j)),
    Nat.beq (pcomp n w (mask w) (GT s.j) (EG (V.ys.getD s.src (nat_lit 0))))
      (pcomp n w (mask w)
        (pcomp n w (mask w) (pw n w z s.a) (pw n w (EG (V.ys.getD s.tgt (nat_lit 0))) s.b))
        (GT s.j)))))))

@[expose] def chainOK (nl : Nat) : List Nat → List CStep → Bool
  | cov, [] => (List.range nl).all fun i => cov.contains i
  | cov, s :: r => cov.contains s.src && chainOK nl (s.tgt :: cov) r

end CFSG.KS.CoreD2K

end

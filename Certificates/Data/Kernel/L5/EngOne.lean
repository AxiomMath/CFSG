module

public import Certificates.Data.Kernel.L5.EngWit

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Fus

variable {n : Nat} [Group (Idx n)]

@[expose] def ctxF (gs : List (Idx n)) : HomCtx n where
  gens := gs
  W := (List.range gs.length).map fun j => (wordsOf (gs.take (j + 1))).map Prod.snd
  R := (List.range gs.length).map fun j => relsOf (gs.take (j + 1)) (wordsOf (gs.take (j + 1)))

@[expose] def pathGo (ctx : HomCtx n) (ci : Array Nat) (ld : List Nat) (tp : Idx n) :
    Nat → Nat → List (Idx n) → List (Idx n) → Bool
  | 0, j, cs, _ => candOK ctx ci ld j cs
  | _ + 1, _, _, [] => false
  | d + 1, j, cs, c :: ps =>
    candOK ctx ci ld j cs && decide (c * tp = tp * c) && pathGo ctx ci ld tp d (j + 1) (cs ++ [c]) ps

@[expose] def hexPath (ctx : HomCtx n) (ci : Array Nat) (ld : List Nat) (tp : Idx n)
    (ps : List (Idx n)) : Bool :=
  pathGo ctx ci ld tp (ctx.gens.length - 1) 1 [tp] ps

@[expose] def scpPath (e : Eng n) (Rs : List (List (Idx n))) (ld : List Nat)
    (Ps : List (List (Idx n))) : Bool :=
  (List.range e.reps.length).all fun k =>
    hexPath (ctxF (e.reps.getD k 1 :: Rs.getD k [])) e.ciA ld (tpOf e ld (ld.getD k 0)) (Ps.getD k [])

@[expose] def survChk (e : Eng n) (Rs : List (List (Idx n))) (ld : List Nat)
    (Ps : List (List (Idx n))) : Bool :=
  xOK e ld && thompsonOK e ld && scpPath e Rs ld Ps

@[expose] def scpDirect (e : Eng n) (Rs : List (List (Idx n))) (ld : List Nat) (k : Nat) : Bool :=
  decide (k < e.reps.length) &&
    !homExists (ctxF (e.reps.getD k 1 :: Rs.getD k [])) e.ciA ld (tpOf e ld (ld.getD k 0))

@[expose] def witOK1 (e : Eng n) (Rs : List (List (Idx n))) (ld₀ ld w : List Nat) : Bool :=
  if w.headD 5 = 3 then decide (ld = ld₀)
  else if w.headD 5 = 4 then scpDirect e Rs ld (w.getD 1 0)
  else witOK e ld w

@[expose] def allWit1 (e : Eng n) (Rs : List (List (Idx n))) (ld₀ : List Nat)
    (ws : List (List Nat)) : Bool :=
  decide (ws.length = (leaders e.reps.length).length) &&
    decide (((leaders e.reps.length).filter fun ld => decide (ld = ld₀)).length = 1) &&
    ((leaders e.reps.length).zip ws).all fun p => witOK1 e Rs ld₀ p.1 p.2

end CFSG.GH74.GLS.C3.Layer2.L5.Fus

end

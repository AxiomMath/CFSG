module

public import CFSG.GH74.GLS.C3.Layer2.L5C2c
public import CFSG.GH74.GLS.C3.Layer2.L5C2a

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Fus

open Equiv Perm CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {n : Nat}

@[expose] def f5PairsF (emb : ↥T5 → Idx n) : List (Idx n × Idx n) :=
  allT5L.flatMap fun (t : ↥T5) => F5list.filterMap fun g =>
    if h : T5b (g * (t : Amb 5) * g⁻¹) = true then
      some (emb t, emb ⟨g * (t : Amb 5) * g⁻¹, mem_T5_of_b h⟩)
    else none

@[expose] def nbarPairsF
    (emb : ↥T5 → Idx n) : List (Idx n × Idx n) :=
  n24L.flatMap fun A => (List.finRange 16).map fun i => (emb (elT i), emb (elT (A i)))

variable [Group (Idx n)]

@[expose] def fuseF
    (emb : ↥T5 → Idx n) : List (Idx n × Idx n) :=
  dedupPairs ((f5PairsF emb ++ nbarPairsF emb).filter fun p => isInv p.1 && isInv p.2)

@[expose] def fusChk
    (emb : ↥T5 → Idx n) (reps : List (Idx n)) (ciA : Array Nat) (invs : List (Idx n))
    (x : Idx n) : Bool :=
  let st := stepsOf (fuseF emb)
  let rs := repsGo st ((elemsI n).filter isInv) (Array.replicate n false) []
  let ms := rs.map (bfs st)
  decide ((elemsI n).filter isInv = invs) && decide (rs = reps) && decide (ciArrOf ms = ciA) &&
    decide (emb x0T5 = x) &&
    reps.all isInv &&
    (List.range reps.length).all (fun k => decide (ciA.getD (reps.getD k 1).v 0 = k)) &&
    invs.all (fun u => decide (ciA.getD u.v 0 < reps.length) &&
      (ms.getD (ciA.getD u.v 0) []).contains u) &&
    isInv x

@[expose] def cszChk (cszA : Array Nat) : Bool := decide (((elemsI n).map cszI).toArray = cszA)

@[expose] def mgChk (mg : List (Idx n)) (ms : List (Array Bool)) : Bool :=
  let wa := wordArrOf mg
  decide (maxSubsOf mg wa = ms) && (elemsI n).all fun m => decide (evW mg (wa.getD m.v []) = m)

@[expose] def ctxR (gens : List (Idx n)) : HomCtx n where
  gens := gens
  W := []
  R := (List.range gens.length).map fun j => relsOf (gens.take (j + 1)) (wordsOf (gens.take (j + 1)))

@[expose] def ctxChk (reps : List (Idx n)) (Rs : List (List (Idx n))) : Bool :=
  (List.range reps.length).all fun k =>
    ctxOK (reps.getD k 1) (ctxR (reps.getD k 1 :: Rs.getD k []))

end CFSG.GH74.GLS.C3.Layer2.L5.Fus

end

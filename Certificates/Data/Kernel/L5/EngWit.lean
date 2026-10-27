module

public import Certificates.Data.Kernel.L5.Greedy
public import Certificates.Data.Kernel.L5.EngScp

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Fus

variable {n : Nat} [Group (Idx n)]

@[expose] def closStep (gs : List (Idx n)) (st : Nat × List (Idx n × List Nat))
    (p : Idx n × List Nat) : Nat × List (Idx n × List Nat) :=
  (List.range gs.length).foldl (fun (st : Nat × List (Idx n × List Nat)) (i : Nat) =>
    if st.1.testBit (p.1 * gs.getD i 1).v then st
    else (st.1 ||| (1 <<< (p.1 * gs.getD i 1).v), st.2 ++ [(p.1 * gs.getD i 1, p.2 ++ [i])])) st

@[expose] def closGo (gs : List (Idx n)) :
    Nat → Nat → List (Idx n × List Nat) → List (Idx n × List Nat) → List (Idx n × List Nat)
  | 0, _, _, acc => acc
  | fuel + 1, vis, fr, acc =>
    match fr.foldl (closStep gs) (vis, []) with
    | (_, []) => acc
    | (vis', nw) => closGo gs fuel vis' nw (acc ++ nw)

@[expose] def closW (gs : List (Idx n)) : List (Idx n × List Nat) :=
  closGo gs n (1 <<< (1 : Idx n).v) [(1, [])] [(1, [])]

@[expose] def prefW (init R : List (Idx n)) : List (List (Idx n × List Nat)) :=
  (List.range (R.length + 1)).map fun j => closW (init ++ R.take j)

@[expose] def genChk (S init R : List (Idx n)) : Bool :=
  (List.range (R.length + 1)).all
      (fun j => subChk (init ++ R.take j) ((prefW init R).getD j [])) &&
    greedySim S R ((prefW init R).map fun W => W.map Prod.fst)

@[expose] def centL (t : Idx n) : List (Idx n) := (elemsI n).filter fun s => decide (s * t = t * s)

@[expose] def ctxGensChk (reps : List (Idx n)) (Rs : List (List (Idx n))) : Bool :=
  decide (Rs.length = reps.length) && (List.range reps.length).all fun k =>
    genChk (centL (reps.getD k 1)) [reps.getD k 1] (Rs.getD k [])

@[expose] def xWit (e : Eng n) (ld : List Nat) (i : Idx n) : Bool :=
  e.invs.contains i && decide (blkOf e.ciA ld i = blkOf e.ciA ld e.x) &&
    decide (32 < e.cszA.getD i.v 0)

@[expose] def thWit (e : Eng n) (ld : List Nat) (h : Nat) (u : Idx n) : Bool :=
  decide (h < e.maxSubs.length) && e.invs.contains u && !(e.maxSubs.getD h #[]).getD u.v false &&
    !(e.invs.any fun i => (e.maxSubs.getD h #[]).getD i.v false &&
      decide (blkOf e.ciA ld i = blkOf e.ciA ld u) &&
      decide (e.cszA.getD i.v 0 = cvalOf e ld (blkOf e.ciA ld u)))

@[expose] def scpWit (e : Eng n) (ld : List Nat) (k : Nat) (τ₀ : Nat × Nat × Nat × Nat) : Bool :=
  decide (k < e.reps.length) &&
    scpRefute e.ciA ld (e.reps.getD k 1) (tpOf e ld (ld.getD k 0)) (centL (e.reps.getD k 1)) τ₀

@[expose] def witOK (e : Eng n) (ld w : List Nat) : Bool :=
  if w.headD 3 = 0 then xWit e ld ((elemsI n).getD (w.getD 1 0) 1)
  else if w.headD 3 = 1 then thWit e ld (w.getD 1 0) ((elemsI n).getD (w.getD 2 0) 1)
  else scpWit e ld (w.getD 1 0) (w.getD 2 0, w.getD 3 0, w.getD 4 0, w.getD 5 0)

@[expose] def allWit (e : Eng n) (ws : List (List Nat)) : Bool :=
  decide (ws.length = (leaders e.reps.length).length) &&
    ((leaders e.reps.length).zip ws).all fun p => witOK e p.1 p.2

end CFSG.GH74.GLS.C3.Layer2.L5.Fus

end

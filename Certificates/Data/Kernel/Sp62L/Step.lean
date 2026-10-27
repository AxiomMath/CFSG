module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData

public section

namespace CFSG.KC.Sp62L

open CFSG.KGroups.Sp6

@[expose] def stepB (gens : List (List ℕ)) (E : Array (List ℕ)) (P : Array (ℕ × ℕ))
    (C POS : ℕ → ℕ) (hd s i : ℕ) : Bool :=
  if hd < C i then
    (decide (POS i ≤ C i) && decide (POS i < E.size) &&
      E.getD (POS i) [] == mulC (E.getD hd []) (gens.getD s [])) &&
    (if POS i = C i then C (i + 1) == C i + 1 && P.getD (C i - 1) (0, 0) == (hd, s) else true) &&
    (if POS i < C i then C (i + 1) == C i else true)
  else C (i + 1) == C i

@[expose] def stepsB (gens : List (List ℕ)) (E : Array (List ℕ)) (P : Array (ℕ × ℕ))
    (C POS : ℕ → ℕ) (fuel : ℕ) : Bool :=
  (List.range fuel).all fun hd => (List.range gens.length).all fun s =>
    stepB gens E P C POS hd s (hd * gens.length + s)

@[expose] def closedB (gens : List (List ℕ)) (E : List (List ℕ)) : Bool :=
  (List.range E.length).all fun v => gens.all fun g => E.contains (mulC (E.toArray.getD v []) g)

@[expose] def replayB (gens : List (List ℕ)) (fuel : ℕ) (E : List (List ℕ)) (P : List (ℕ × ℕ))
    (C POS : List ℕ) : Bool :=
  E.toArray.getD 0 [] == oneC && decide (0 < E.length) && decide E.Nodup &&
    P.length + 1 == E.length && C.getD 0 0 == 1 &&
    stepsB gens E.toArray P.toArray (fun i => C.getD i 0) (fun i => POS.getD i 0) fuel &&
    C.getD (fuel * gens.length) 0 == E.length &&
    CFSG.Quasithin.G2U.build oneC mulC gens P == E.toArray && closedB gens E

end CFSG.KC.Sp62L

end

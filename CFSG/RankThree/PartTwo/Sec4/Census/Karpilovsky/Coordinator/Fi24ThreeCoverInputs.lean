module

public import CFSG.Sporadic.Recognition.Fi24PrimeMultiplierInputs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.CosetTable CFSG.Sporadic.Presentation.Fi24Prime
  CFSG.Sporadic.Recognition.Fi24PrimeMultiplier

@[expose] def repIdx3 : List ℕ := [36, 54, 70, 84, 96, 106, 114, 120, 126, 128, 134]

@[expose] def sqIdx : ℕ := 16

@[expose] def centralWords3 : List (List (Fin nG × Bool)) :=
  (List.range 11).flatMap fun k =>
    [(X0.getD (repIdx3.getD k 0) []).map liftL ++ [(zeta k, false)],
      List.replicate 9 (zeta k, true)] ++
    (List.range 11).map fun i =>
      [(zeta k, true), (Fin.ofNat nG i, true), (zeta k, false), (Fin.ofNat nG i, false)]

@[expose] def wsQ : List (List (Fin nG × Bool)) :=
  (X0.filter fun w => !(w.any fun l => l.1.val == 8)).map (·.map liftL) ++
    [(X0.getD sqIdx []).map liftL] ++ centralWords3

@[expose] def zetaWord (k : ℕ) : List (Fin nG × Bool) := [(zeta k, true)]

@[expose] def qWords : List (List (Fin nG × Bool) × ℕ) := [(zetaWord 10, 3)]

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

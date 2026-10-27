module

public import CFSG.Sporadic.Presentation.Fi24PrimeExactInputs

public section

namespace CFSG.Sporadic.Recognition.Fi24PrimeMultiplier

open CFSG.CosetTable CFSG.Sporadic.Presentation.Fi24Prime

abbrev m0 : ℕ := TauCeti.SporadicName.Fi24Prime.presentation.generatorCount

abbrev nG : ℕ := 22

@[expose] def liftL (l : Fin m0 × Bool) : Fin nG × Bool :=
  (⟨l.1.val % nG, Nat.mod_lt _ (by norm_num)⟩, l.2)

@[expose] def zeta (k : ℕ) : Fin nG := Fin.ofNat nG (11 + k)

@[expose] def repIdx : List ℕ := [16, 36, 54, 70, 84, 96, 114, 120, 126, 128, 134]

abbrev S0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 9, 10]

abbrev PG10 : Type := PG (subsetOf m0 S0).length X1

@[expose] def r0Idx : ℕ := 106

@[expose] def centralWords : List (List (Fin nG × Bool)) :=
  (List.range 11).flatMap fun k =>
    [(X0.getD (repIdx.getD k 0) []).map liftL ++ [(zeta k, false)],
      [(zeta k, true), (zeta k, true)]] ++
    (List.range 11).map fun i =>
      [(zeta k, true), (Fin.ofNat nG i, true), (zeta k, false), (Fin.ofNat nG i, false)]

@[expose] def wsN : List (List (Fin nG × Bool)) :=
  (X0.filter fun w => !(w.any fun l => l.1.val == 8)).map (·.map liftL) ++
    [(X0.getD r0Idx []).map liftL] ++ centralWords

end CFSG.Sporadic.Recognition.Fi24PrimeMultiplier

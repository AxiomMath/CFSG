module

public import CFSG.RankThree.PartOne.K159.AutCoreFive

public section

namespace CFSG.RankThree.PartOne.K159

open Matrix MatrixGroups
open CFSG.RankThree.PartOne.K159F
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section PSL2

variable {K : Type*} [Field K] [Finite K]

theorem autWitnessUpTo_six_psl_two {p : ℕ} [CharP K p] (hcard : p ^ 2 ≤ Nat.card K)
    (hbig : 13 < Nat.card K) : AutWitnessUpTo 6 p PSL(2, K) :=
  autWitnessN_psl_two (m := 2) (B := 6) hcard (by omega)

end PSL2

theorem autWitnessUpTo_six_of_isoLie_A1_two {p : ℕ} (hp5 : 5 ≤ p) {S : Type} [Group S]
    (q : TauCeti.PrimePower) (hqp : q.p = p) (hq : q.exponent = 2) (h : IsoLie S (.A 1 q)) :
    AutWitnessUpTo 6 p S := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e⟩ := nonempty_psl_two_of_isoLie q h
  subst hqp
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ 2 := by
    rw [GaloisField.card q.p q.exponent (by omega), hq]
  refine AutWitnessUpTo.of_mulEquiv e.symm
    (autWitnessUpTo_six_psl_two (K := GaloisField q.p q.exponent) (p := q.p) (hcard.ge) ?_)
  rw [hcard]
  nlinarith

end CFSG.RankThree.PartOne.K159

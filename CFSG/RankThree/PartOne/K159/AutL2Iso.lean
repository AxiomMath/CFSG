module

public import CFSG.RankThree.PartOne.K159.AutL2
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.RankThree.PartOne.K159

open Matrix MatrixGroups
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem nonempty_psl_two_of_isoLie {S : Type} [Group S] (q : TauCeti.PrimePower)
    [Fact q.p.Prime] (h : IsoLie S (.A 1 q)) :
    Nonempty (S ≃* PSL(2, GaloisField q.p q.exponent)) := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  exact ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)⟩

theorem autWitness_of_isoLie_A1_two {p : ℕ} (hp5 : 5 ≤ p) {S : Type} [Group S]
    (q : TauCeti.PrimePower) (hqp : q.p = p) (hq : q.exponent = 2) (h : IsoLie S (.A 1 q)) :
    AutWitness p S := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e⟩ := nonempty_psl_two_of_isoLie q h
  subst hqp
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ 2 := by
    rw [GaloisField.card q.p q.exponent (by omega), hq]
  refine AutWitness.of_mulEquiv e.symm (autWitness_psl_two (K := GaloisField q.p q.exponent) (p := q.p) (hcard.ge) ?_)
  rw [hcard]
  nlinarith

theorem bigWitness_of_isoLie_A1_three {p : ℕ} {S : Type} [Group S]
    (q : TauCeti.PrimePower) (hqp : q.p = p) (hq : q.exponent = 3) (h : IsoLie S (.A 1 q)) :
    BigWitness p S := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e⟩ := nonempty_psl_two_of_isoLie q h
  subst hqp
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ 3 := by
    rw [GaloisField.card q.p q.exponent (by omega), hq]
  refine BigWitness.of_mulEquiv e.symm (bigWitness_psl_two (K := GaloisField q.p q.exponent) (p := q.p) ?_)
  rw [hcard]
  exact Nat.pow_lt_pow_right q.prime_p.one_lt (by norm_num)

end CFSG.RankThree.PartOne.K159

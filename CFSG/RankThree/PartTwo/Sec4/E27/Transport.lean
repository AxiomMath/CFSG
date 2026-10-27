module

public import CFSG.RankThree.PartTwo.Sec4.E27.FamilySU
public import CFSG.RankThree.PartTwo.Sec4.E27.FamilySp
public import CFSG.RankThree.PartTwo.Sec4.E27.FixG2

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP CFSG.Assembly.LowTwoRank
open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.AGLEmbeddingD2

namespace CFSG.RankThree.PartTwo.Sec4.E27

section SpSU


theorem seitz27_projSp {n : ℕ} (hn : 4 ≤ n) :
    Seitz27 (CFSG.PGLModel.projSp 2 (GaloisField 2 n)) :=
  seitz27_of_mulEquiv (CFSG.PGLModel.projSpEquivStatedProj 2 (GaloisField 2 n))
    (seitz27_sp4 (f := n) hn (GaloisField.card 2 n (by omega)))

theorem seitz27_projSU4 {n : ℕ} (hn : 4 ≤ n) :
    Seitz27 (CFSG.Assembly.RankThreeEven.projSU 4 2 n) := by
  have hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
    CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField 2 n (by omega)
  haveI := hU.finite
  have hne : ¬ (4 = 3 ∧ 2 ^ n = 2) := by omega
  let ψ : primeFormP hU (idGram (GaloisField 2 (2 * n)) 4) ≃*
      StatedProj (StatedSU 4 (2 ^ n) (GaloisField 2 (2 * n))) :=
    (Classical.choice (unitary_prime_form_full_semilinear_realization hU
      (isPrimeFormGram_idGram (K := GaloisField 2 (2 * n)) (n := 4)) (by norm_num) hne).1).trans
      (unitaryPSUEquiv hU (by omega))
  exact seitz27_of_mulEquiv ((CFSG.PGLModel.projSUEquivStatedProj 4 2 n).trans ψ.symm)
    (seitz27_su4 hU hn)

end SpSU



theorem seitz27_isoGTwo {X : Type} [Group X] (q : PrimePower) (hq : q.p = 2) (hn : 4 ≤ q.exponent)
    (hX : CFSG.RankThree.PartTwo.Sec4.IsoGTwo X q) : Seitz27 X := by
  obtain ⟨hv, ⟨e⟩⟩ := hX
  obtain ⟨K, _, _, hK, -⟩ := CFSG.LieType.SeitzGeneration.exists_field_pow q (m := 1) Nat.one_pos
  rw [pow_one] at hK
  obtain ⟨e2⟩ := catEquiv_g2 (k := K) q hv hK
  refine seitz27_of_mulEquiv (e.trans e2) (seitz27_g2 (f := q.exponent) hn ?_)
  rw [hK, PrimePower.card_def, hq]

end CFSG.RankThree.PartTwo.Sec4.E27

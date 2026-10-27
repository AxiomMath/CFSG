module

public import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness
import CFSG.RankThree.PartOne.Census3.LinearWitness
public import CFSG.LocalAnalysis.SectionRank.QTK.OddTorusU

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.Assembly CFSG.Assembly.LowTwoRank Matrix
open CFSG.Assembly.RankThreeEven (projSL projSU localRank)
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Census (torusSL torusSL_injective coe_torusSL torusEntries
  torusEntries_of_gt torusEntries_injective prod_torusEntries torusEntries_compLeft
  rootsOfUnity_pow_eq_one card_fun_rootsOfUnity card_rootsOfUnity_of_dvd isElemAbelian_range
  le_localRank_quotient_of_commute diagGL localRank_eq_of_mulEquiv)

variable {K : Type} [Field K]

export CFSG.SectionRank.QTK (twoSign det_diagonal_twoSign twoSign_mul_self
  diagonal_twoSign_mul_self twoSign_zero_ne_two twoSignSL twoSignGL le_localRank_PSL_torus_odd
  le_localRank_statedSU_torus_odd)

theorem three_le_localRank_projSL_four_odd (p : ℕ) [Fact p.Prime] (hp : 3 < p) (h1 : p % 3 = 1)
    [Finite (projSL 4 (GaloisField p 1))] : 3 ≤ localRank 3 (projSL 4 (GaloisField p 1)) := by
  have hK : Nat.card (GaloisField p 1) = p := by
    rw [GaloisField.card p 1 one_ne_zero, pow_one]
  have h2 : (2 : GaloisField p 1) ≠ 0 :=
    CFSG.RankThree.PartOne.Census3.two_ne_zero_of_charP (p := p) (by omega)
  rw [← localRank_eq_of_mulEquiv (pslEquivProjSL 4 (GaloisField p 1)) Nat.prime_three]
  refine le_localRank_PSL_torus_odd h2 (m := 3) Nat.prime_three ?_ (by norm_num) (by norm_num)
    (Or.inr (by norm_num))
  rw [Nat.card_units, hK]
  omega

theorem three_le_localRank_projSU_four_odd (p : ℕ) [Fact p.Prime] (hp : 3 < p) (h2 : p % 3 = 2)
    [Finite (projSU 4 p 1)] : 3 ≤ localRank 3 (projSU 4 p 1) := by
  have hu := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField p 1 le_rfl
  rw [← localRank_eq_of_mulEquiv (statedSUEquivProjSU 4 p 1) Nat.prime_three]
  exact le_localRank_statedSU_torus_odd hu (by omega) (m := 3) Nat.prime_three
    (by rw [pow_one]; omega) (by norm_num) (by norm_num) (Or.inr (by norm_num))

theorem three_le_localRank_projSL_four_four [Finite (projSL 4 (GaloisField 2 2))] :
    3 ≤ localRank 3 (projSL 4 (GaloisField 2 2)) := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  rw [← localRank_eq_of_mulEquiv (pslEquivProjSL 4 (GaloisField 2 2)) Nat.prime_three]
  exact CFSG.RankThree.PartTwo.Census.le_localRank_PSL_torus (m := 3) Nat.prime_three
    (by rw [Nat.card_units, hK]) (by norm_num) (by norm_num) (Or.inr (by norm_num))

theorem three_le_localRank_projSU_two {n f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1) (hn : 5 ≤ n)
    (hcen : 6 ≤ n ∨ ¬ 3 ∣ n) [Finite (projSU n 2 f)] : 3 ≤ localRank 3 (projSU n 2 f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField 2 f hf
  rw [← localRank_eq_of_mulEquiv (statedSUEquivProjSU n 2 f) Nat.prime_three]
  exact CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus (k := 2) hu Nat.prime_three h3
    (by omega) (by rcases hcen with h | h; exacts [Or.inl (by omega), Or.inr h])

theorem le_localRank_projSL_three {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    [Finite (projSL 3 (GaloisField p e))] : e ≤ localRank p (projSL 3 (GaloisField p e)) := by
  rw [← localRank_eq_of_mulEquiv (pslEquivProjSL 3 (GaloisField p e)) Fact.out]
  exact CFSG.RankThree.PartOne.Census3.le_localRank_PSL_three hp2
    (GaloisField.card p e (by omega))

theorem le_localRank_projSU_three {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    [Finite (projSU 3 p e)] : e ≤ localRank p (projSU 3 p e) := by
  have hu := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField p e he
  rw [← localRank_eq_of_mulEquiv (statedSUEquivProjSU 3 p e) Fact.out,
    ← localRank_eq_of_mulEquiv (unitaryPSUEquiv hu (n := 3) (by norm_num)) Fact.out]
  exact le_trans (by rw [one_pow, mul_one])
    (CFSG.RankThree.PartTwo.Census.le_localRank_unitaryPSU hu hp2 (n := 3) (r := 1) le_rfl
      (by norm_num))

end CFSG.RankThree.PartTwo.Sec4.Census

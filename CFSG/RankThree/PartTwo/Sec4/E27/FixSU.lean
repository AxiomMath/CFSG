module

public import CFSG.RankThree.PartTwo.Sec4.E27.InnerOuter
public import CFSG.RankThree.PartTwo.Sec4.E27.FieldAutSUOdd
public import CFSG.LieType.SeitzGeneration.FixPlaneGenUnitary

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP CFSG.Assembly.LowTwoRank
open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open

namespace CFSG.RankThree.PartTwo.Sec4.E27


theorem seitz27_su4_of_inner {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (hf : 4 ≤ f)
    (hZ : Subgroup.center (primeFormP h (idGram K 4)) = ⊥)
    (hinner : ∀ E : Subgroup (primeFormP h (idGram K 4)), IsElemAbelian 3 E → Nat.card E = 27 →
      HyperGen 3 (⊤ : Subgroup (primeFormP h (idGram K 4))) E) :
    Seitz27 (primeFormP h (idGram K 4)) := by
  haveI := h.finite
  have hg : ¬ 3 ∣ Nat.gcd 4 (2 ^ f + 1) := by
    intro hd
    have : 3 ∣ 4 := hd.trans (Nat.gcd_dvd_left _ _)
    omega
  have hne : ¬ (4 = 3 ∧ 2 ^ f = 2) := by omega
  have h8 : ¬ (3 = 3 ∧ 2 ^ f = 8) := by
    rintro ⟨-, h8⟩
    have : 2 ^ f ≤ 2 ^ 3 := by omega
    have := Nat.pow_le_pow_iff_right (by norm_num : 1 < 2) |>.1 this
    omega
  have hF : FieldAutData (primeFormP h (idGram K 4)) 3 := by
    refine fieldAutData_primeFormP_of_ne_two h (by norm_num) hne Nat.prime_three (by norm_num)
      (by norm_num) hg ?_
    intro f₀ hf₀ h2
    have h1 : f₀ = 1 := Nat.pow_right_injective (le_refl 2) (by simpa using h2)
    omega
  have hP : FixPlaneGen (primeFormP h (idGram K 4)) 3 :=
    fixPlaneGen_primeFormP h (by norm_num) hne Nat.prime_three (by norm_num) (by norm_num) hg h8
  exact seitz27_of_inner_outer hZ hinner hF hP

end CFSG.RankThree.PartTwo.Sec4.E27

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax
public import CFSG.GroupTheory.TwoResidualOddOrder
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem inU_of_uniqueMax {M X : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (h : UniqueMax M X) : UC6.InU M X where
  left := by
    have hmem : M ∈ calMOf X := by rw [h]; exact Set.mem_singleton M
    exact hmem.2
  right := by
    intro g hXg
    have hmax : rankThreeIsMaxTwoLocal (uniqueFourConj g M) :=
      UC6.isMaxTwoLocal_conj (show IsMaxTwoLocalSubgroup M from hM) g
    have hmem : uniqueFourConj g M ∈ calMOf X := ⟨hmax, hXg⟩
    rw [h] at hmem
    exact Set.mem_singleton_iff.mp hmem

theorem twoResidual_not_le_conjSubgroup_of_inU {M X H : Subgroup G} {g : G}
    (hM : Subgroup.normalizer (M : Set G) = M) (hU : UC6.InU M X)
    (hXH : X ≤ twoResidual H) (hg : g ∉ M) :
    ¬ twoResidual H ≤ conjSubgroup M g := by
  intro hle
  have hXg : X ≤ uniqueFourConj g M := hXH.trans hle
  exact (UC6.inU_iff_not_le hM).1 hU |>.2 g hg hXg

theorem twoResidual_not_le_conjSubgroup_of_uniqueMax {M X H : Subgroup G} {g : G}
    (hM : rankThreeIsMaxTwoLocal M) (hUX : UniqueMax M X)
    (hXH : X ≤ twoResidual H) (hg : g ∉ M) :
    ¬ twoResidual H ≤ conjSubgroup M g :=
  twoResidual_not_le_conjSubgroup_of_inU
    (UC6.normalizer_eq_of_isMaxTwoLocal (show IsMaxTwoLocalSubgroup M from hM))
    (inU_of_uniqueMax hM hUX) hXH hg

theorem le_twoResidual_of_odd_prime_card {H X : Subgroup G} {q : ℕ}
    (hXH : X ≤ H) (hq : q.Prime) (hq2 : q ≠ 2) (hcard : Nat.card X = q) :
    X ≤ twoResidual H :=
  CFSG.GroupTheory.le_twoResidual_of_odd_card hXH (hcard ▸ hq.odd_of_ne_two hq2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

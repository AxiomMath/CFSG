module

public import CFSG.RankThree.PartOne.F106.OddRadAt
import CFSG.RankThree.PartOne.F106.OddRadSpInner
import CFSG.RankThree.PartOne.F106.OddRadSpTwo
import CFSG.RankThree.PartOne.F106.OddRadSpOuter
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem oddRadAt_smallModel_psp : OddRadAt (SmallModel .PSp) := by
  rintro T _ _ _ ⟨n, f, hadm, hmodel, hsmall⟩ β hβ
  have hn2 : 2 ≤ n := hadm.2.2.1
  have hn4 : n ≤ 4 := hsmall
  rcases hmodel with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl
    have : Finite (StatedProj (StatedSp n K)) := Finite.of_equiv T e.toEquiv
    have hf1 : 1 ≤ f := hadm.2.1
    have hrq : ¬ (n = 2 ∧ 2 ^ f = 2) := fun h => hadm.2.2.2 (by rw [h.1, h.2])
    refine oddRadConcl_of_mulEquiv e (fun β' hβ' => ?_) β hβ
    by_cases hI : β' ∈ inner (StatedProj (StatedSp n K))
    · obtain ⟨a, rfl⟩ := hI
      have hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp n K) →*
          MulAut (StatedProj (StatedSp n K))) := (spProj_facts Nat.prime_two hf1 hK hn2 hrq).2.2
      have ha : orderOf a = 5 := by rw [← hβ', orderOf_injective _ hinj a]
      by_cases hf2 : 2 ≤ f
      · exact OddRadSp.oddRadConcl_conj_sp hK hf2 (by omega) a ha
      · have hf1' : f = 1 := by omega
        subst hf1'
        have hn3 : 3 ≤ n := by
          by_contra h3
          exact hrq ⟨by omega, by norm_num⟩
        exact OddRadSp.oddRadConcl_conj_sp_two (by simpa using hK) hn3 hn4 a ha
    · exact OddRadSp.oddRadConcl_outer_sp hn2 hf1 hK β' hβ' hI
  all_goals exact absurd h0 (by omega)

end CFSG.RankThree.PartOne.F106

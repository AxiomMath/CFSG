module

public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofStatements
public import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJTrivial

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.Blueprint CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ

theorem gap128OTwoHJ :
    Gap128OTwoHJ := by
  intro X _ _ hX hperf ⟨e⟩
  set θ := aschbacherSolvableCore 3 X with hθdef
  obtain ⟨hθsol, -, hθ3, -, -, -, hθO⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  let π : X →* NativeSporadic.J2 := e.toMonoidHom.comp (QuotientGroup.mk' θ)
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective θ)
  have hker : π.ker = θ := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ x ∈ θ
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hK : Group.IsSolvable π.ker := by
    rw [hker]
    exact hθsol
  have h3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hker]
    exact hθ3
  have hθ2 : θ ≤ CFSG.pCore 2 X := by
    rw [← hker]
    by_cases hO2 : CFSG.pCore 2 X = ⊥
    · rw [ker_eq_bot_of_localRank π hπ hK h3 hO2 hX.localRank_lt]
      exact bot_le
    · refine ker_le_pCore_two_of_pRank_le_two π hπ hK h3 fun p hp hp3 => ?_
      have h1 := pRank_le_localRank_of_le_normalizer hp hO2 pCore_isPGroup
        (H := ⊤) (Subgroup.normalizer_eq_top (CFSG.pCore 2 X)).ge
      rw [pRank_congr_mulEquiv hp.one_lt Subgroup.topEquiv] at h1
      have h2 := hX.localRank_lt p hp hp3
      omega
  have heq : CFSG.pCore 2 X = θ := le_antisymm (hθO 2 Nat.prime_two (by norm_num)) hθ2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans e⟩

end CFSG.RankThree.PartTwo.Sec12

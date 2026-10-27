module

public import CFSG.RankThree.PartTwo.Late.Defs
import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.Hyperplane

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G}

theorem le_of_le_normalizer_of_isPiSubgroup (hAM : Sec18Std G A M) {X : Subgroup G}
    (hX : IsPiSubgroup (piCompl 3) X) (hAX : A ≤ Subgroup.normalizer (X : Set G)) : X ≤ M := by
  have hE : IsE27 A := isE27_of_mem_partTwoE hAM.mem_partTwoE
  have hgM : gamma 2 A ≤ M :=
    SetLike.coe_subset_coe.mp (CFSG.RankThree.PartTwo.mem_scriptM_iff.mp hAM.mem_scriptM).2
  have hcop : Nat.Coprime 3 (Nat.card X) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => ?_
    have h := hX ⟨3, Nat.prime_three⟩ h3
    exact h rfl
  have hgen := CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.generation_hyperplanes
    Nat.prime_three hE.1 (by rw [hE.2]; norm_num) hAX hcop
  have hpB : ∀ B : Subgroup G, B ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 3 A →
      2 ≤ CFSG.Open.pRank 3 B := by
    intro B hB
    have hcardB : Nat.card B = 9 := by
      have h := hB.2
      rw [hE.2] at h
      omega
    have hBel := CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 3 hE.1 hB.1
    exact le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three B)
      ⟨B, le_rfl, hBel, by norm_num [hcardB]⟩
  refine (le_of_eq hgen.symm).trans (iSup₂_le fun B hB => ?_)
  refine inf_le_right.trans ?_
  exact (Subgroup.centralizer_le_normalizer _).trans
    ((CFSG.RankThree.PartTwo.normalizer_le_gamma hB.1 (hpB B hB)).trans hgM)

end CFSG.RankThree.PartTwo.Sec18.Item187Proof

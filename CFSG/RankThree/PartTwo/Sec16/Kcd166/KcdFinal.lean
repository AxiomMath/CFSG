module

public import CFSG.RankThree.PartTwo.Sec16.Kcd166.KcdReduce
public import CFSG.RankThree.PartTwo.Sec16.Kcd166.MainAlg
import CFSG.RankThree.PartTwo.Sec16.Kcd166.FixRank
import CFSG.RankThree.PartTwo.Sec16.Kcd166.MainAlgProof

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem gFlatAt166_of_mainAlg166 (hmain : MainAlg166) : GFlatAt166 := by
  intro G _ _ p hp hp3 hloc X hXperf hT d hd3 hdZ I₁ hI₁p hI₁d hI₁2 hI₁A5
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three (by omega) (by omega)
  obtain ⟨hθs, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  have hker : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)).ker =
      aschbacherSolvableCore 3 ↥X := QuotientGroup.ker_mk' _
  have hR3 : ∀ N M : Subgroup ↥X, N.Normal → M.Normal → N ≤ M →
      (∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) → (∀ x ∈ M, x ^ p ∈ N) →
      ∀ t : ↥X, IsPGroup 2 (Subgroup.zpowers t) → (∃ m ∈ M, t * m * t⁻¹ * m⁻¹ ∉ N) →
      ∀ F : Subgroup ↥X, N ≤ F → F ≤ M → (∀ f ∈ F, t * f * t⁻¹ * f⁻¹ ∈ N) →
        N.relIndex F ≤ p ^ 3 := by
    intro N M hN hM hNM hab hexp t ht2 htnt F hNF hFM hFt
    haveI := hN
    haveI := hM
    refine relIndex_le_pow_three hp5
      (card_le_sq_subgroup (card_le_sq_of_localRank_lt hp hloc) X) hNM (hN.subgroupOf M) hab
      hexp ht2 ?_ ?_ htnt hNF hFM hFt
    · rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top t
    · rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top t
  intro N M hN hM hNM hMθ
  refine gflat_of_mainAlg166 hmain hXperf (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))
    (QuotientGroup.mk'_surjective _) hT (by rw [hker]; exact hθs)
    (by rw [hker]; exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3).symm)
    hp5 hR3 hd3 hdZ hI₁p hI₁A5 (by rw [hker]; exact hI₁2) hI₁d N M hN hM hNM
    (by rw [hker]; exact hMθ)

theorem step166KcdA5_of_mainAlg166
    (hmain : MainAlg166) : Step166KcdA5 :=
  step166KcdA5_of_gFlatAt166 (gFlatAt166_of_mainAlg166 hmain)

theorem step166KcdA5_holds :
    Step166KcdA5 :=
  step166KcdA5_of_mainAlg166 mainAlg166_holds

end CFSG.RankThree.PartTwo.Sec16.Kcd166

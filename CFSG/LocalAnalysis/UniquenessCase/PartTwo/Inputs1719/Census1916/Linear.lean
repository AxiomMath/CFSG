module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Census1916.Defs
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Psl
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Census1916

open CFSG.Open
open CFSG.RankThree.PartTwo.Sec19.Census194

theorem census1916SurvPSL_holds :
    Census1916SurvPSL := by
  intro Y _ _ n f hR hm hn5
  have hf1 : 1 ≤ f := hm.1.2.1
  obtain ⟨⟨-, -, hn2, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have : Group.IsPerfect Y := hR.quasisimple.1
  have hodd := RonanC194.odd_card_center_of_pCore_eq_bot hR.pCore_two
  obtain ⟨φ, hφs, hker, hD⟩ :=
    CFSG.SectionRank.EvenCover.even_linear_perfect_odd_cover_map hn2 hodd e
  have hDn := (RonanC194.card_scalars_statedSL_dvd (K := K) (n := n) (by omega)).1
  have hDq := (RonanC194.card_scalars_statedSL_dvd (K := K) (n := n) (by omega)).2
  have hkerD : Nat.card φ.ker ∣
      Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) :=
    Subgroup.card_dvd_of_le hker
  let eY : StatedSL n K ⧸ φ.ker ≃* Y := QuotientGroup.quotientKerEquivOfSurjective φ hφs
  have htorus : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ f - 1 →
      n - 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedSL n K ⧸ φ.ker)) ∧
      (¬ r ∣ Nat.card φ.ker →
        n - 1 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedSL n K ⧸ φ.ker))) := by
    intro r hr hr2 hrd
    have : Fact r.Prime := ⟨hr⟩
    exact CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank Nat.prime_two hn2 hr2
      (Or.inl ⟨hK, rfl, hrd⟩) φ.ker hker
  have hf_eq : f = 1 := by
    by_contra hf
    have hf2 : 2 ≤ f := by omega
    obtain ⟨r, hr, hr2, hr5, hrd⟩ :=
      CFSG.RankThree.PartTwo.Census.exists_prime_ne_five_dvd_two_pow_sub_one hf2
    have h4 : 4 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedSL n K ⧸ φ.ker)) := by
      rcases Nat.lt_or_ge n 6 with hn6 | hn6
      · have hn5' : n = 5 := by omega
        subst hn5'
        refine (by omega : 4 ≤ 5 - 1).trans ((htorus r hr hr2 hrd).2 ?_)
        intro hrk
        have h5 : r ∣ 5 := hrk.trans (hkerD.trans (by simpa using hDn))
        exact hr5 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).1 h5)
      · exact (by omega : 4 ≤ n - 2).trans ((htorus r hr hr2 hrd).1)
    exact hR.false_of_mulEquiv eY hr hr2 h4
  refine ⟨hf_eq, ?_⟩
  by_contra hn
  have hn8 : 8 ≤ n := by omega
  subst hf_eq
  have hD1 : Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) = 1 := by
    have h1 : Nat.card K - 1 = 1 := by rw [hK]; norm_num
    exact Nat.dvd_one.1 (h1 ▸ hDq)
  have hDbot : (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ hD1
  have hZ : Subgroup.center Y = ⊥ := by rw [← hD, hDbot, Subgroup.map_bot]
  let e' : Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
    ((RonanC194.mulEquivQuotientCenterOfEqBot hZ).trans e).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm
  have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) := Finite.of_equiv Y e'.toEquiv
  have h4 : 4 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) K)) :=
    (CFSG.RankThree.PartTwo.Census.four_le_localRank_PSL_of_eight_le hn8).trans
      (RonanC194.localRank_le_pRank Nat.prime_three)
  exact hR.false_of_mulEquiv e'.symm Nat.prime_three (by norm_num) h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Census1916

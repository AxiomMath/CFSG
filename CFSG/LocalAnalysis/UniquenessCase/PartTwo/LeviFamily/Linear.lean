module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.CensusDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Parabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.BlocksSL
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Index
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphAltEightLevi
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem exists_comap_eq_flagStabilizer_of_psl {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) {J : Subgroup S} (hJ : S19.IsNontrivialParabolic S J) {n : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hn : 2 ≤ n) (e : S ≃* projectiveSL n K) :
    ∃ (σ : Matrix.SpecialLinearGroup (Fin n) K →* ↥(⊤ : Subgroup S)) (I : Set ℕ),
      Function.Surjective σ ∧
      σ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) ∧
      (J.subgroupOf (⊤ : Subgroup S)).comap σ = flagStabilizer n K I := by
  classical
  have hZtop : Subgroup.center ↥(⊤ : Subgroup S) = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    rw [Nat.card_congr
      (Subgroup.centerCongr (Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S)).toEquiv,
      center_eq_bot_of_isNontrivialParabolic hS hJ, Subgroup.card_bot]
  have hcomm : commutator ↥(⊤ : Subgroup S) = ⊤ := by
    have hP : Group.IsPerfect S :=
      Group.isPerfect_def.mpr (commutator_eq_top_of_isNontrivialParabolic hS hJ)
    exact Group.isPerfect_def.mp (Group.IsPerfect.top_iff.mpr hP)
  let e' : ↥(⊤ : Subgroup S) ⧸ Subgroup.center ↥(⊤ : Subgroup S) ≃* projectiveSL n K :=
    (QuotientGroup.quotientMulEquivOfEq hZtop).trans
      (QuotientGroup.quotientBot.trans (Subgroup.topEquiv.trans e))
  obtain ⟨ρ, hρ⟩ := CFSG.AGLEmbedding.ToralCensus.exists_compat_of_center_eq_bot hZtop e'
  obtain ⟨hρs, hρk⟩ :=
    CFSG.AGLEmbedding.ToralCensus.surjective_and_ker_le_of_compat hcomm e' ρ hρ
  have hodd : Odd (Nat.card (Subgroup.center ↥(⊤ : Subgroup S))) := by
    rw [hZtop, Subgroup.card_bot]
    exact odd_one
  obtain ⟨σ, e'', I, hσs, hσ, -, hcomap, -, -⟩ :=
    CFSG.AGLEmbedding.exists_comap_eq_flagStabilizer (n := n) (K := K) hodd (by omega) e' hρs hρ
      (isParabolicTwo_top_of_isNontrivialParabolic hJ)
  obtain ⟨-, hσk⟩ :=
    CFSG.AGLEmbedding.ToralCensus.surjective_and_ker_le_of_compat hcomm e'' σ hσ
  exact ⟨σ, I, hσs, hσk, hcomap⟩

private theorem card_linBlockSL_ne_bot_mul_two_le {K : Type} [Field K] [Finite K] [CharP K 2]
    (n : ℕ) (I : Set ℕ) :
    Nat.card {a : Fin n // linBlockSL K n I a ≠ ⊥} * 2 ≤ n := by
  classical
  have hiff : ∀ a : Fin n, (linBlockSL K n I a = ⊥ ↔ linBlockLen n I a ≤ 1) :=
    fun a => range_toGL_eq_bot_iff (K := K) (linBlockLen n I a)
  have hcard : Nat.card {a : Fin n // linBlockSL K n I a ≠ ⊥} =
      (Finset.univ.filter fun a : Fin n => 2 ≤ linBlockLen n I a).card := by
    rw [Nat.card_eq_fintype_card]
    refine Fintype.card_of_subtype _ fun a => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ne_eq, hiff a]
    omega
  have hsum : (∑ a ∈ Finset.univ.filter (fun a : Fin n => 2 ≤ linBlockLen n I a),
      linBlockLen n I a) ≤ ∑ a : Fin n, linBlockLen n I a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Nat.zero_le _
  have h2 : (Finset.univ.filter fun a : Fin n => 2 ≤ linBlockLen n I a).card * 2 ≤
      ∑ a ∈ Finset.univ.filter (fun a : Fin n => 2 ≤ linBlockLen n I a),
        linBlockLen n I a := by
    simpa using Finset.card_nsmul_le_sum
      (Finset.univ.filter fun a : Fin n => 2 ≤ linBlockLen n I a)
      (fun a => linBlockLen n I a) 2 (fun a ha => (Finset.mem_filter.mp ha).2)
  have hsl := CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.AltEight.sum_linBlockLen_le n I
  rw [hcard]
  omega

private theorem censusAlt_linBlockSL {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}
    (hnf : n ≤ 4 ∨ f = 1) (hf : 1 ≤ f) (hKcard : Nat.card K = 2 ^ f) (I : Set ℕ) :
    CensusAlt (G := fun a : Fin n => GL (Fin (linBlockLen n I a)) K) (linBlockSL K n I) := by
  classical
  by_cases hf1 : f = 1
  · right
    intro a hq m hm
    exact not_isL2_range_toGL (K := K) (by rw [hKcard, hf1]; norm_num) (linBlockLen n I a) hq
      (n := m) hm
  · left
    have hn4 : n ≤ 4 := hnf.resolve_right hf1
    have hf2 : 2 ≤ f := by omega
    have hKne : Nat.card K ≠ 2 := by
      rw [hKcard]
      have h4 : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      omega
    refine ⟨?_, fun a => range_toGL_eq_bot_or_isQuasisimple hKne (linBlockLen n I a)⟩
    have hcnt := card_linBlockSL_ne_bot_mul_two_le (K := K) n I
    omega

private theorem blockFacts_linBlockSL {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}
    (hf : 1 ≤ f) (hKcard : Nat.card K = 2 ^ f) (I : Set ℕ) :
    BlockFacts (f = 1) (6 ≤ n) (linBlockSL K n I) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro a hq
    have hne : linBlockSL K n I a ≠ ⊥ := by
      rw [← Subgroup.nontrivial_iff_ne_bot]
      have hnt : Nontrivial (↥(linBlockSL K n I a) ⧸
          Subgroup.center ↥(linBlockSL K n I a)) := hq.2.toNontrivial
      exact (QuotientGroup.mk'_surjective (Subgroup.center ↥(linBlockSL K n I a))).nontrivial
    have hm : 2 ≤ linBlockLen n I a := by
      by_contra h
      exact hne ((range_toGL_eq_bot_iff (K := K) (linBlockLen n I a)).mpr (by omega))
    exact three_dvd_card_quotient_center_range_toGL (K := K) hm
  · intro a h3
    by_contra hf1
    have hf2 : 2 ≤ f := by omega
    have hKne : Nat.card K ≠ 2 := by
      rw [hKcard]
      have h4 : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      omega
    rcases range_toGL_eq_bot_or_isQuasisimple (K := K) hKne (linBlockLen n I a) with hbot | hq
    · exact not_nonempty_mulEquiv_perm_three (Or.inl hbot) h3
    · exact not_nonempty_mulEquiv_perm_three (Or.inr hq) h3
  · by_cases h6 : 6 ≤ n
    · exact Or.inr h6
    · refine Or.inl ?_
      have hcnt := card_linBlockSL_ne_bot_mul_two_le (K := K) n I
      omega

private theorem hasLeviDataX_of_psl_of_model {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) {n f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKcard : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f) (hnf : n ≤ 4 ∨ f = 1) (hn2 : 2 ≤ n)
    (eS : S ≃* StatedProj (StatedSL n K)) {J : Subgroup S}
    (hJ : S19.IsNontrivialParabolic S J) : HasLeviDataX (f = 1) (6 ≤ n) ↥J := by
  classical
  have hn1 : 1 ≤ n := by omega
  let eStated : StatedProj (StatedSL n K) ≃* projectiveSL n K :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  obtain ⟨σ, I, hσs, hσk, hcomap⟩ :=
    exists_comap_eq_flagStabilizer_of_psl hS hJ hn2 (eS.trans eStated)
  set β : ↥((J.subgroupOf (⊤ : Subgroup S)).comap σ) →*
      ∀ a : Fin n, GL (Fin (linBlockLen n I a)) K :=
    (linLeviHom K n I).comp (MulEquiv.subgroupCongr hcomap).toMonoidHom with hβdef
  have hβrange : β.range = (linLeviHom K n I).range := by
    rw [hβdef, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (MulEquiv.subgroupCongr hcomap).surjective, Subgroup.map_top]
  have ho : Odd (Nat.card σ.ker) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_dvd_of_le hσk)
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
      (CFSG.RankThree.PartTwo.Census.coprime_card_center_SL (K := K) hn1).symm
  refine hasLeviDataX_of_cover (X := S) (C := Matrix.SpecialLinearGroup (Fin n) K) (L := ⊤)
    (J := J) (ι := Fin n) (G := fun a : Fin n => GL (Fin (linBlockLen n I a)) K)
    (S := linBlockSL K n I) le_top σ hσs hσk ho β ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have hβeq : β.ker = (linLeviHom K n I).ker.comap
        (MulEquiv.subgroupCongr hcomap).toMonoidHom := by
      rw [hβdef]
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_comap]
    rw [hβeq]
    exact IsPGroup.comap_of_injective (isPGroup_ker_linLeviHom hn1)
      (MulEquiv.subgroupCongr hcomap).toMonoidHom (MulEquiv.subgroupCongr hcomap).injective
  · rw [hβrange]
    exact pi_le_range_linLeviHom
  · rw [hβrange]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.le_normalizer_of_commutator_le
      pi_le_range_linLeviHom commutator_range_linLeviHom_le
  · have hidx : ¬ 2 ∣ (Subgroup.pi Set.univ (linBlockSL K n I)).relIndex
        (linLeviHom K n I).range := by
      refine CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.not_two_dvd_relIndex_pi
        (k := n) (G := fun a : Fin n => GL (Fin (linBlockLen n I a)) K)
        (S := linBlockSL K n I) (T := fun _ => ⊤) (fun _ => le_top) pi_le_range_linLeviHom ?_ ?_
      · rw [Subgroup.pi_top]
        exact le_top
      · intro a
        rw [Subgroup.relIndex_top_right]
        exact CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.not_two_dvd_index_range_toGL
          (K := K) (linBlockLen n I a)
    rwa [hβrange]
  · intro a
    exact range_toGL_eq_bot_or_isLeviBlock (K := K) (linBlockLen n I a)
  · exact censusAlt_linBlockSL (n := n) (f := f) hnf hf1 hKcard I
  · exact blockFacts_linBlockSL hf1 hKcard I

theorem hasLeviDataX_of_psl {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) {n f : ℕ}
    (h : CFSG.Blueprint.LieModel S .PSL n 2 f) (hnf : n ≤ 4 ∨ f = 1) {J : Subgroup S}
    (hJ : S19.IsNontrivialParabolic S J) : HasLeviDataX (f = 1) (6 ≤ n) ↥J := by
  obtain ⟨-, hf1, hn2, -, -⟩ := h.admissible
  obtain ⟨-, K, _, _, hKcard, ⟨eS⟩⟩ := h.statedClassicalModel_of_ne_zero (by omega)
  have : CharP K 2 :=
    @charP_of_card_eq_prime_pow K _ _ (Fintype.ofFinite K) 2 f ⟨Nat.prime_two⟩ (by
      rw [← @Nat.card_eq_fintype_card K (Fintype.ofFinite K)]
      exact hKcard)
  exact hasLeviDataX_of_psl_of_model hS hKcard hf1 hnf hn2 eS hJ

theorem hasLeviData_of_psl {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) {n f : ℕ}
    (h : CFSG.Blueprint.LieModel S .PSL n 2 f) (hnf : n ≤ 4 ∨ f = 1) {J : Subgroup S}
    (hJ : S19.IsNontrivialParabolic S J) : HasLeviData ↥J :=
  (hasLeviDataX_of_psl hS h hnf hJ).hasLeviData

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

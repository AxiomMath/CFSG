module

public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.GroupTheory.ABGLocalTools.PStabilityChief
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.GroupTheory.K462SLTwoQuotient
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XOddQuot
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddInv
import CFSG.LocalAnalysis.WeakClosure81.W15SixC
import CFSG.Quasithin.Background.F918Z4c2Real
import CFSG.GroupTheory.PerfectNormalConjugate
import CFSG.Adapters.StatedPSLTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem isSLn_of_isL2 {X : Type} [Group X] {m : ℕ} (h : IsL2 X m) :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsSLn X 2 m := by
  rw [CFSG.LocalAnalysis.WeakClosure81.isL2_iff_isPSL] at h
  obtain ⟨K, hKf, hKfin, _hchar, hKcard, _hn2, ⟨e⟩⟩ := CFSG.Quasithin.Z4c2.exists_equiv_sl h
  exact ⟨K, hKf, hKfin, hKcard,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)⟩⟩

private theorem eq_top_of_le_normalizer_of_isL2 {K B D : Subgroup G} {m : ℕ} (hK : ⁅K, K⁆ = K)
    (hL2 : IsL2 (Bar2 K) m) (hBK : B ≤ K) (hKn : K ≤ normalizer (B : Set G))
    (hDB : D ≤ B) (hD3 : Nat.card D = 3) : B = K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsimple : IsSimpleGroup (Bar2 K) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
  have hBnorm : (B.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBK).mpr hKn
  haveI := hBnorm
  have hDK : D ≤ K := hDB.trans hBK
  have hD3K : Nat.card (D.subgroupOf K) = 3 := by
    rw [← hD3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv
  have hDsub_le : D.subgroupOf K ≤ B.subgroupOf K := Subgroup.subgroupOf_mono K hDB
  have hDsub_p : IsPGroup 3 ↥(D.subgroupOf K) :=
    IsPGroup.of_card (n := 1) (by simpa using hD3K)
  have hdisj : Disjoint (D.subgroupOf K) (CFSG.pCore 2 ↥K) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hDsub_p CFSG.pCore_isPGroup
  have hDnot : ¬ D.subgroupOf K ≤ CFSG.pCore 2 ↥K := by
    intro hle
    have hbot : D.subgroupOf K = ⊥ := by
      have h := hdisj.eq_bot
      rwa [inf_eq_left.mpr hle] at h
    rw [hbot, Subgroup.card_bot] at hD3K
    omega
  rcases CFSG.GroupTheory.le_or_sup_eq_top_of_normal_of_isSimpleGroup_quotient
      (N := CFSG.pCore 2 ↥K) (K := B.subgroupOf K) hsimple with hle | hsup
  · exact absurd (hDsub_le.trans hle) hDnot
  · have hP : IsPGroup 2 (↥K ⧸ B.subgroupOf K) := by
      let q : ↥K →* (↥K ⧸ B.subgroupOf K) := QuotientGroup.mk' (B.subgroupOf K)
      have hmap : (CFSG.pCore 2 ↥K).map q = ⊤ := by
        have h := congrArg (Subgroup.map q) hsup
        rw [Subgroup.map_sup, QuotientGroup.map_mk'_self,
          Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _), bot_sup_eq] at h
        exact h
      have hp : IsPGroup 2 ↥((CFSG.pCore 2 ↥K).map q) := CFSG.pCore_isPGroup.map q
      rw [hmap] at hp
      exact hp.of_equiv Subgroup.topEquiv
    haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
    have htop : B.subgroupOf K = ⊤ :=
      CFSG.ComponentClassification.LiteratureLocal.eq_top_of_isPGroup_quotient_of_perfect
        (p := 2) (B.subgroupOf K) hP
    exact le_antisymm hBK (Subgroup.subgroupOf_eq_top.mp htop)

private theorem chief_quot_cases_of_isL2 (hK462 : UCK.K462) {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hKk : CFSG.Open.IsKGroup ↥K) {m : ℕ} (hL2 : IsL2 (Bar2 K) m)
    {r : ℕ} [Fact r.Prime] (hr : 2 < r) {W₁ W₂ : Subgroup G}
    (hW : CFSG.ABGLocalTools.IsChiefFactorUnder r K W₁ W₂) {D : Subgroup G} (hDK : D ≤ K)
    (hD3 : Nat.card D = 3)
    (hfix : ∀ w ∈ W₁, (∀ d ∈ D, w * d * w⁻¹ * d⁻¹ ∈ W₂) → w ∈ W₂) :
    ∃ (N : Subgroup ↥K) (_ : N.Normal), ¬ 3 ∣ Nat.card N ∧
      ((∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧
          Nonempty (↥K ⧸ N ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
        (∃ n : ℕ, Odd n ∧ CFSG.Blueprint.LieModel (↥K ⧸ N) .PSL 2 2 n) ∨
        CFSG.Quasithin.IsExt (↥K ⧸ N)
          (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
          (fun Y _ => CFSG.Quasithin.IsAlt 5 Y)) := by
  have hE9 : ¬ CFSG.GroupTheory.ThreeTranspositions.HasE9 ↥K := by
    intro h
    have h2 := h.two_le_pRank
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K] at h2
    have h1 : CFSG.Open.pRank 3 K = 1 :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.pRank_three_eq_one_of_isL2 hL2
    omega
  have hfix' : ∀ u ∈ W₁, (∀ x ∈ D, x * u * x⁻¹ * u⁻¹ ∈ W₂) → u ∈ W₂ := by
    intro u hu h
    apply hfix u hu
    intro d hd
    have hmem := W₂.inv_mem (h d hd)
    rwa [show (d * u * d⁻¹ * u⁻¹)⁻¹ = u * d * u⁻¹ * d⁻¹ by group] at hmem
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.chief_quot_cases_odd hK462 hKk hE9 hK
    hDK hD3 (fun B hBK hKn hDB => eq_top_of_le_normalizer_of_isL2 hK hL2 hBK hKn hDB hD3)
    (Fact.out : r.Prime) (by omega) hW hfix'

theorem false_of_isChiefFactorUnder_of_isL2 (hK462 : UCK.K462) {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hKk : CFSG.Open.IsKGroup ↥K) {m : ℕ} (hm4 : 4 ≤ m) (hme : Even m) (hL2 : IsL2 (Bar2 K) m)
    {r : ℕ} [Fact r.Prime] (hr : 2 < r) {W₁ W₂ : Subgroup G}
    (hW : CFSG.ABGLocalTools.IsChiefFactorUnder r K W₁ W₂) {D : Subgroup G} (hDK : D ≤ K)
    (hD3 : Nat.card D = 3) (hfix : ∀ w ∈ W₁, (∀ d ∈ D, w * d * w⁻¹ * d⁻¹ ∈ W₂) → w ∈ W₂) :
    False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨N, hNnormal, hN3, hcases⟩ :=
    chief_quot_cases_of_isL2 hK462 hK hKk hL2 hr hW hDK hD3 hfix
  letI := hNnormal
  have hsimple : IsSimpleGroup (Bar2 K) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
  have h3dvd : 3 ∣ Nat.card (Bar2 K) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.three_dvd_card_of_isL2Even hL2
  have hNle : N ≤ CFSG.pCore 2 ↥K :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.le_pCore_two_of_normal hsimple h3dvd hN3
  let f : (↥K ⧸ N) →* Bar2 K :=
    QuotientGroup.lift N (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (by
      intro x hx
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥K) x).mpr (hNle hx))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) y
    exact ⟨QuotientGroup.mk' N x, QuotientGroup.lift_mk' N _ x⟩
  exact CFSG.GroupTheory.not_surjective_of_k462_alternative hm4 hme
    (isSLn_of_isL2 hL2) hcases f hf

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

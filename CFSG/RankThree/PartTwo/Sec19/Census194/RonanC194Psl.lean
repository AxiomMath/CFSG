module

public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Core
public import CFSG.RankThree.PartTwo.Sec19.Census194.Arith
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearCover
public import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover
public import CFSG.RankThree.PartTwo.Census.Classical.EvenBlocks
public import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

open CFSG CFSG.RankThree.PartTwo.Sec19 CFSG.Assembly.LowTwoRank

section Scalars

variable {K : Type} [Field K] [Finite K]

theorem card_scalars_statedSL_dvd {n : ℕ} (hn : 1 ≤ n) :
    Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) ∣ n ∧
      Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) ∣ Nat.card K - 1 := by
  refine ⟨CFSG.SectionRank.OddCover.card_scalars_dvd hn _ fun x c hc => ?_,
    CFSG.SectionRank.OddCover.card_scalars_dvd hn _ fun x c _ => ?_⟩
  · have hdet := CFSG.SectionRank.OddCover.det_of_mem_statedSL x.1.2
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
  · rw [← CFSG.SectionRank.OddCover.card_units_eq]
    exact pow_card_eq_one'

end Scalars

theorem localRank_le_pRank {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) :
    CFSG.Assembly.RankThreeEven.localRank p G ≤ CFSG.Open.pRank p (⊤ : Subgroup G) :=
  CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank p hp G

theorem survPSL_holds :
    Census194SurvPSL := by
  intro Y _ _ n f hR hm hn4
  have hf1 : 1 ≤ f := hm.1.2.1
  obtain ⟨⟨-, -, hn2, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have : Group.IsPerfect Y := hR.quasisimple.1
  have hodd := odd_card_center_of_pCore_eq_bot hR.pCore_two
  obtain ⟨φ, hφs, hker, hD⟩ :=
    CFSG.SectionRank.EvenCover.even_linear_perfect_odd_cover_map hn2 hodd e
  by_contra hcon
  have hcases : (3 ≤ f ∧ 4 ≤ n) ∨ (f = 2 ∧ 5 ≤ n) ∨ (f = 1 ∧ 8 ≤ n) := by omega
  have hDn := (card_scalars_statedSL_dvd (K := K) (n := n) (by omega)).1
  have hDq := (card_scalars_statedSL_dvd (K := K) (n := n) (by omega)).2
  have hkerD : Nat.card φ.ker ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) :=
    Subgroup.card_dvd_of_le hker
  let eY : StatedSL n K ⧸ φ.ker ≃* Y := QuotientGroup.quotientKerEquivOfSurjective φ hφs
  have hTB : TooBig (StatedSL n K ⧸ φ.ker) → False := fun h =>
    hR.false_of_tooBig (h.of_mulEquiv eY)
  have htorus : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ f - 1 →
      n - 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedSL n K ⧸ φ.ker)) ∧
      (¬ r ∣ Nat.card φ.ker →
        n - 1 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedSL n K ⧸ φ.ker))) := by
    intro r hr hr2 hrd
    haveI : Fact r.Prime := ⟨hr⟩
    exact CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank Nat.prime_two hn2 hr2
      (Or.inl ⟨hK, rfl, hrd⟩) φ.ker hker
  rcases hcases with ⟨hf3, hn4'⟩ | ⟨rfl, hn5⟩ | ⟨rfl, hn8⟩
  ·
    obtain ⟨r, hr, hr3, hrd⟩ := exists_prime_gt_three_dvd_two_pow_sub_one hf3
    obtain ⟨h1, h2⟩ := htorus r hr (by omega) hrd
    rcases Nat.lt_or_ge n 5 with h5 | h5
    · obtain rfl : n = 4 := by omega
      have hrk : ¬ r ∣ Nat.card φ.ker := fun h => by
        have h4 : r ∣ 2 ^ 2 := by simpa using h.trans (hkerD.trans hDn)
        have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h4)
        omega
      exact hTB (tooBig_of_prime hr hr3 (by have := h2 hrk; omega))
    · exact hTB (tooBig_of_prime hr hr3 (by omega))
  ·
    obtain ⟨h1, h2⟩ := htorus 3 Nat.prime_three (by norm_num) (by norm_num)
    rcases Nat.lt_or_ge n 6 with h6 | h6
    · obtain rfl : n = 5 := by omega
      have hrk : ¬ 3 ∣ Nat.card φ.ker := fun h => by
        have h4 : 3 ∣ 5 := h.trans (hkerD.trans hDn)
        omega
      exact hTB (tooBig_of_three (by have := h2 hrk; omega))
    · exact hTB (tooBig_of_three (by omega))
  ·
    have hD1 : Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) = 1 := by
      have h1 : Nat.card K - 1 = 1 := by rw [hK]; norm_num
      exact Nat.dvd_one.1 (h1 ▸ hDq)
    have hDbot : (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ hD1
    have hZ : Subgroup.center Y = ⊥ := by rw [← hD, hDbot, Subgroup.map_bot]
    let e' : Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
      ((mulEquivQuotientCenterOfEqBot hZ).trans e).trans
        (projectiveSpecialLinearGroupEquivStatedProj n K).symm
    have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) := Finite.of_equiv Y e'.toEquiv
    have h4 : 4 ≤ CFSG.Open.pRank 3
        (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) K)) :=
      (CFSG.RankThree.PartTwo.Census.four_le_localRank_PSL_of_eight_le hn8).trans
        (localRank_le_pRank Nat.prime_three)
    exact hR.false_of_tooBig ((tooBig_of_three h4).of_mulEquiv e'.symm)

theorem idPSL_holds :
    Census194IdPSL := by
  intro Y _ _ n f hR hm hn3 hcase
  have hf1 : 1 ≤ f := hm.1.2.1
  have hmodel := hm
  obtain ⟨⟨-, -, hn2, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have : Group.IsPerfect Y := hR.quasisimple.1
  have hodd := odd_card_center_of_pCore_eq_bot hR.pCore_two
  obtain ⟨φ, hφs, hker, hD⟩ :=
    CFSG.SectionRank.EvenCover.even_linear_perfect_odd_cover_map hn2 hodd e
  obtain ⟨eP⟩ := CFSG.RankThree.PartOne.projSL_of_statedClassicalModel hmodel
  have hDn := (card_scalars_statedSL_dvd (K := K) (n := n) (by omega)).1
  have hDq := (card_scalars_statedSL_dvd (K := K) (n := n) (by omega)).2
  rw [hK] at hDq
  have hkerD : Nat.card φ.ker ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) :=
    Subgroup.card_dvd_of_le hker
  have hg : Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) ∣
      Nat.gcd n (2 ^ f - 1) := Nat.dvd_gcd hDn hDq
  have hZbot : n ≠ 3 → Subgroup.center Y = ⊥ := by
    intro hn3'
    have hgcd : Nat.gcd n (2 ^ f - 1) = 1 := by
      rcases hcase with h | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩
      · exact absurd h hn3'
      all_goals norm_num
    have hD1 : Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) = 1 :=
      Nat.dvd_one.1 (hgcd ▸ hg)
    rw [← hD, Subgroup.eq_bot_of_card_eq _ hD1, Subgroup.map_bot]
  by_cases hZ : Subgroup.center Y = ⊥
  ·
    have eY : Y ≃* CFSG.PGLModel.projSL n (GaloisField 2 f) :=
      (mulEquivQuotientCenterOfEqBot hZ).trans eP
    rcases hcase with rfl | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩
    · exact Or.inl ⟨f, hf1, Or.inr (Or.inl ⟨eY⟩)⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨eY⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eY⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eY⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eY⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eY⟩)))))))
  ·
    have hn3' : n = 3 := by
      by_contra h
      exact hZ (hZbot h)
    subst hn3'
    left
    refine ⟨f, hf1, Or.inl ?_⟩
    have hD1 : Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) ≠ 1 := by
      intro h
      apply hZ
      rw [← hD, Subgroup.eq_bot_of_card_eq _ h, Subgroup.map_bot]
    have hD3 : Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) = 3 :=
      ((Nat.dvd_prime Nat.prime_three).1 hDn).resolve_left hD1
    have hkerbot : φ.ker = ⊥ := by
      rcases (Nat.dvd_prime Nat.prime_three).1 (hD3 ▸ hkerD) with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        have heq : φ.ker = (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) :=
          Subgroup.eq_of_le_of_card_ge hker (by rw [h3, hD3])
        apply hZ
        rw [← hD, ← heq, Subgroup.map_eq_bot_iff]
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hkerbot
    let eφ : StatedSL 3 K ≃* Y := MulEquiv.ofBijective φ ⟨hinj, hφs⟩
    let ψ : K ≃+* GaloisField 2 f :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 f hf1 hK
    exact ⟨eφ.symm.trans (((MulEquiv.subgroupMap (CFSG.Adapters.RankTwoModelTransports.glCongr ψ)
      (StatedSL 3 K)).trans (MulEquiv.subgroupCongr
        (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSL ψ 3))).trans
      (specialLinearGroupEquivStatedSL 3 (GaloisField 2 f)).symm)⟩

end CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

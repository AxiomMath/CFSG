module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XD
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101USyl
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101USp
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UCnt
import CFSG.LocalAnalysis.UniquenessCase.UC22S13a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3b
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Fusion
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem u81_mem_uniqueSet_of_dvd {M R B A : Subgroup G} {p r : ℕ} [Fact p.Prime]
    [Fact r.Prime] (hsp : IsStronglyPEmbedded p M) (hR : CFSG.ABGLocalTools.IsSylowOf r R M)
    (hBR : B ≤ R) (hBel : IsElemAbelian r B) (hΩ : ∀ x ∈ R, x ^ r = 1 → x ∈ B) (hAB : A ≤ B)
    (hNA : normalizer (A : Set G) ≤ M) (hdvd : p ∣ Nat.card (centralizer (B : Set G))) :
    A ∈ uniqueSet M :=
  CFSG.LocalAnalysis.AGL81TheoremCD.Section8.mem_uniqueSet_of_normalizer_le_of_omega hR hBR hBel
    hΩ (hsp.normalizer_le_of_centralizer_le
      (((Subgroup.centralizer_le hAB).trans (Subgroup.centralizer_le_normalizer _)).trans hNA)
      hdvd) hAB hNA

namespace U4X

variable {D : Data G} {L K : Subgroup G} {n : ℕ}

theorem u81_dvd_of_inf_eq_bot (u : U4X D L K n)
    (hsp : IsStronglyPEmbedded n D.M) (hfour : 4 ≤ CFSG.Open.pRank n D.M) {R B : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf (2 ^ n - 1) R D.M) (hBR : B ≤ R)
    (hΩ : ∀ x ∈ R, x ^ (2 ^ n - 1) = 1 → x ∈ B)
    (hB0 : barImage D.M B ⊓ centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) = ⊥) :
    n ∣ Nat.card (centralizer (B : Set G)) := by
  have hn2 : n ≠ 2 := by rcases u.hLS with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  obtain ⟨c, hcC, hco⟩ := u.u81_exists_mem_centralizer hsp hfour
  refine u81_dvd_card_centralizer (hBR.trans hR.le) u.prime_r u.r_ne_two
    (hR.isPGroup.to_le hBR) u.prime_n hn2 hco (mem_centralizer_iff.2 fun β hβ => ?_)
  obtain ⟨x₀, hx₀, x₁, hx₁, c', hc', rfl⟩ := u.u81_omega_decomp hR hBR hΩ hβ
  rw [hB0, Subgroup.mem_bot] at hc'
  rw [hc', mul_one]
  exact Commute.mul_left (mem_centralizer_iff.1 hcC x₀ (mem_sup_left hx₀.2))
    (mem_centralizer_iff.1 hcC x₁ (mem_sup_right hx₁.2))

theorem u81_mem_uniqueSet_of_residual (u : U4X D L K n)
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D) (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h847 : F08.R847 D) (he : 3 < CFSG.Open.evenRank G)
    (hnsp : ¬ IsStronglyPEmbedded (2 ^ n - 1) D.M)
    (hres : ∀ R B : Subgroup G, CFSG.ABGLocalTools.IsSylowOf (2 ^ n - 1) R D.M → B ≤ R →
      R ≤ centralizer (B : Set G) → IsElemAbelian (2 ^ n - 1) B →
      (∀ x ∈ R, x ^ (2 ^ n - 1) = 1 → x ∈ B) → CFSG.Open.pRank (2 ^ n - 1) D.M ≤ 3 →
      CFSG.Open.pRank n (centralizer
        ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M))) ≤ 1 →
      barImage D.M B ⊓ centralizer
        ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) ≠ ⊥ →
      ¬ n ∣ Nat.card (centralizer (B : Set G)) → normalizer (B : Set G) ≤ D.M)
    {A : Subgroup G} (hAL : A ≤ L) (hAr : Nat.card A = 2 ^ n - 1) :
    A ∈ uniqueSet D.M := by
  have hns := UC6S846.not_solvable_of_mem_calC u.hL
  have hsp := UC6S846.sp_of_mem_sig hSg hns u.hσ
  have hr := u.prime_r
  haveI : Fact n.Prime := ⟨u.prime_n⟩
  haveI : Fact (2 ^ n - 1).Prime := ⟨hr⟩
  have hr3 : CFSG.Open.pRank (2 ^ n - 1) D.M ≤ 3 := by
    by_contra h4
    exact hnsp (UC6S846.sp_of_mem_sig hSg hns (hSg.four_mem _ hr u.r_ne_two (by omega)))
  have hAp : IsPGroup (2 ^ n - 1) A := IsPGroup.of_card (n := 1) (by rw [hAr, pow_one])
  obtain ⟨R, hR, hAR⟩ := PartTwo.exists_isSylowOf_ge_of_isPGroup hAp (hAL.trans u.hL.1.le)
  obtain ⟨B, hBR, hRB, hBel, hΩ⟩ := u.u81_exists_omega hr3 hR
  have hAB : A ≤ B := fun x hx => hΩ x (hAR hx) (by
    have h := pow_card_eq_one' (x := (⟨x, hx⟩ : ↥A))
    rw [hAr] at h
    exact congrArg Subtype.val h)
  have hNA : normalizer (A : Set G) ≤ D.M :=
    r847Four_of_r847 D h847 he L u.hL A hAL _ hr u.r_ne_two hAr n u.hσ
      (uc22s13a_thin8_of_isL2_or_isSz u.shape)
  by_cases hdvd : n ∣ Nat.card (centralizer (B : Set G))
  · exact u81_mem_uniqueSet_of_dvd hsp hR hBR hBel hΩ hAB hNA hdvd
  have hB0 : barImage D.M B ⊓ centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) ≠ ⊥ := fun h =>
    hdvd (u.u81_dvd_of_inf_eq_bot hsp (hfour n u.hσ) hR hBR hΩ h)
  have hC1 : CFSG.Open.pRank n (centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M))) ≤ 1 := by
    by_contra h2
    exact hnsp (u.u81_sp_of_two_le_pRank hSg h614 h76 (by omega))
  exact CFSG.LocalAnalysis.AGL81TheoremCD.Section8.mem_uniqueSet_of_normalizer_le_of_omega hR hBR
    hBel hΩ (hres R B hR hBR hRB hBel hΩ hr3 hC1 hB0 hdvd) hAB hNA

end U4X

end CFSG.LocalAnalysis.UniquenessCase.UC22

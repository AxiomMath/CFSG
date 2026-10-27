module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UseS5
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Good
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvable
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Good
import CFSG.LocalAnalysis.UniquenessCase.UC7P3NoBad
import CFSG.LocalAnalysis.UniquenessCase.UC22SigmaThreeStrong
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem solvable_or_of_stronglyEmbeddedSolvable_of_kIDExcluded (k : Sec7Core4 G) (h5 : 5 ≤ k.p)
    (hno : KIDExcluded k) {H : Subgroup G} (hH : Config k H) (h75 : Step75 k)
    (hS : StronglyEmbeddedSolvable) :
    IsSolvable ↥(((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) ∨
      (k.p = 5 ∧
        (Nat.card ↥(((H ⊓ k.M).subgroupOf H).map
          (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)))).factorization 5 ≤ 2 ∧
        ∀ Y : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H),
          Y ≤ ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) →
          ⁅Y, Y⁆ = Y → Nat.card Y ≤ 3600) := by
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper k.standing.kProper hH.ne_top
  exact hS k.p hp h5 _
    (CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH (CFSG.pPrimeCore k.p ↥H))
    (CFSG.pPrimeCore_quotient_eq_bot hp) (k.two_le_pRank_quotient_pPrimeCore hH) _
    (k.isStronglyPEmbedded_map_quotient_pPrimeCore hH) (hno H hH h75)

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvable StronglyEmbeddedThree BadNoStrongThree Sec7Core4)

variable {G : Type} [Group G] [Finite G]

namespace R869S

theorem normalizer_le_of_solvable_or (hG : IsSimpleGroup G) {p r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {M L A : Subgroup G} (hLM : L ≤ M) (hLperf : ⁅L, L⁆ = L)
    (h2 : 2 ≤ CFSG.Open.pRank p L) (h5 : p = 5 → 2 ^ 12 ∣ Nat.card (Bar2 L)) (hr : r.Prime)
    (hAM : A ≤ M) (hAr : Nat.card A = r)
    (hY : (L ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 L = L)
    (hK : ∀ H : Subgroup G, H ≠ ⊤ → ¬ H ≤ M → 2 ≤ CFSG.Open.pRank p (H ⊓ M) →
      IsSolvable ↥(((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) ∨
        (p = 5 ∧ Odd (Nat.card (CFSG.pPrimeCore p ↥H)) ∧
          ∀ Y : Subgroup (↥H ⧸ CFSG.pPrimeCore p ↥H),
            Y ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) →
            ⁅Y, Y⁆ = Y → Nat.card Y ≤ 3600)) :
    normalizer (A : Set G) ≤ M := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hHM
  have hYL : L ⊓ centralizer (A : Set G) ≤ L := inf_le_left
  have hYH : L ⊓ centralizer (A : Set G) ≤ normalizer (A : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hYM : L ⊓ centralizer (A : Set G) ≤ M := hYL.trans hLM
  have hrank : 2 ≤ CFSG.Open.pRank p (normalizer (A : Set G) ⊓ M) :=
    h2.trans ((pRank_le_of_sup_pCore hYL hY hp hp2).trans
      (CFSG.SectionRank.pRank_mono hp.one_lt (le_inf hYH hYM)))
  have htop : normalizer (A : Set G) ≠ ⊤ := by
    intro htop
    haveI : A.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases (inferInstance : A.Normal).eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.card_bot] at hAr
      exact hr.one_lt.ne hAr
    · exact hHM (le_top.trans (h ▸ hAM))
  have hdvd := card_bar2_dvd hYL hYH hY hLperf (CFSG.pPrimeCore p ↥(normalizer (A : Set G)))
  have hYN : ((L ⊓ centralizer (A : Set G)).subgroupOf (normalizer (A : Set G))).map
      (QuotientGroup.mk' (CFSG.pPrimeCore p ↥(normalizer (A : Set G)))) ≤
      ((normalizer (A : Set G) ⊓ M).subgroupOf (normalizer (A : Set G))).map
        (QuotientGroup.mk' (CFSG.pPrimeCore p ↥(normalizer (A : Set G)))) :=
    Subgroup.map_mono (Subgroup.comap_mono (le_inf hYH hYM))
  rcases hK _ htop hHM hrank with hsol | ⟨hp5, hodd, hle⟩
  ·
    haveI : Group.IsSolvable ↥(((normalizer (A : Set G) ⊓ M).subgroupOf
        (normalizer (A : Set G))).map
          (QuotientGroup.mk' (CFSG.pPrimeCore p ↥(normalizer (A : Set G))))) := hsol
    have hsY : Group.IsSolvable ↥(((L ⊓ centralizer (A : Set G)).subgroupOf
        (normalizer (A : Set G))).map
          (QuotientGroup.mk' (CFSG.pPrimeCore p ↥(normalizer (A : Set G))))) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hYN)
    rw [CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot] at hsY
    rw [hsY, Subgroup.card_bot, one_mul] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd hp).1
      (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥(normalizer (A : Set G))))
      ((dvd_card_bar2 hp hp2 (by omega)).trans hdvd)
  ·
    have h12 := (Nat.Coprime.pow_left 12 hodd.coprime_two_left).dvd_of_dvd_mul_right
      ((h5 hp5).trans hdvd)
    have hle' := hle _ ((CFSG.Quasithin.perfectCore_le _).trans hYN)
      (CFSG.Quasithin.perfectCore_perfect _)
    have h4096 := Nat.le_of_dvd Nat.card_pos h12
    norm_num at h4096
    omega

end R869S

theorem r869NS5_dataOfSetup4_of_mem_beta (hSS : StronglyEmbeddedSolvable)
    (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree) (hB : BadNoStrongThree)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma)
    (h3 : 3 ∈ uniqueFourBeta G) : F08.R869NS5 (dataOfSetup4 hS hU S) := by
  rintro L hLM hML hprod ⟨p, hp, h2, h5⟩ r hr hr2 A hAM hAr hY
  have hpp : p.Prime := hp.1.1
  have hp2 : p ≠ 2 := hp.1.2.1
  have hLperf := R869S.perfect_of_isProdOfCalC hprod
  have hL1 : L ≠ ⊥ := by
    rintro rfl
    obtain ⟨E, hE, -, hcard⟩ := CFSG.SectionRank.exists_pRank hpp.one_lt (⊥ : Subgroup G)
    rw [le_bot_iff.1 hE, Subgroup.card_bot] at hcard
    have := Nat.one_lt_pow (by omega : CFSG.Open.pRank p (⊥ : Subgroup G) ≠ 0) hpp.one_lt
    omega
  have hns : ¬ Group.IsSolvable ↥(dataOfSetup4 hS hU S).M := by
    intro hs
    have hsL : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLM)
    rw [CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot,
      CFSG.Quasithin.perfectCore_eq_self_of_perfect hLperf] at hsL
    exact hL1 hsL
  have hsp := UC6S846.sp_of_mem_sig (UC6S846.sigmaStd_dataOfSetup4 hS hU S) hns hp
  let k : Sec7Core4 G := Sec7Core4.ofSetup4Any hS hU S hp hsp
  have h3M := UC22.isStronglyPEmbedded_three_of_mem_uniqueFourBeta hU S hσ h3
  refine R869S.normalizer_le_of_solvable_or hS.simple hpp hp2 hLM hLperf h2 h5 hr hAM hAr hY
    fun H htop hHM hrank => ?_
  have hH : k.Config H := ⟨htop, hHM, hrank⟩
  by_cases hp3 : p = 3
  · exact Or.inl (k.kInputThree hp3 hK3 hH).2.2.2
  · have h5k : 5 ≤ k.p := Nat.Prime.five_le_of_ne_two_of_ne_three hpp hp2 hp3
    rcases k.solvable_or_of_stronglyEmbeddedSolvable_of_kIDExcluded h5k
        (k.kIDExcluded_of_strongThree h5k h3M hB) hH (k.step75 h5k hSE) hSS with
      hsol | ⟨hp5, -, hle⟩
    · exact Or.inl hsol
    · exact Or.inr ⟨hp5, k.odd_card_pPrimeCore_of_not_le hHM hrank, hle⟩

theorem r869NS5_dataOfSetup4_of_inMSigma (hSS : StronglyEmbeddedSolvable)
    (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree) (hB : BadNoStrongThree)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) :
    F08.R869NS5 (dataOfSetup4 hS hU S) := by
  by_cases h3 : 3 ∈ uniqueFourBeta G
  · exact r869NS5_dataOfSetup4_of_mem_beta hSS hSE hK3 hB hS hU S hσ h3
  · exact r869NS5_dataOfSetup4 hSS hSE hS hU S h3

end CFSG.LocalAnalysis.UniquenessCase.UC6

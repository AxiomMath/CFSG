module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09Shape92A5N
import CFSG.ClassicalGroups.PCoreSection
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Perfect
import CFSG.LocalAnalysis.UniquenessCase.UCFront09Shape92A5Holds
import CFSG.LocalAnalysis.UniquenessCase.UCFront09Shape92A5NJ1L2
import CFSG.LocalAnalysis.UniquenessCase.UCFront09Shape92A5NL3U3
import CFSG.RankThree.PartTwo.KFacts.KS166J2A5Alt5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem card_dvd_eight_of_isAlt_five {S : Type} [Group S] [Finite S]
    (hBT : ∀ W X : Subgroup S, W ≠ ⊥ → IsPGroup 2 W → ⁅X, X⁆ = X →
      X ≤ normalizer (W : Set S) → X = ⊥)
    {K T : Subgroup S} (hA5 : IsAlt (Bar2 K) 5) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set S)) : Nat.card T ∣ 8 := by
  obtain ⟨P, -, hPP, -, hNKP, hA5P, -⟩ := exists_perfect_core_of_isAlt_five hA5
  have hP1 : P ≠ ⊥ := by
    intro h
    have h60 := card_eq_sixty_mul_of_isAlt_five hA5P
    have h1 : Nat.card P = 1 := by
      rw [h]
      exact Subgroup.card_bot
    omega
  have hO : CFSG.pCore 2 P = ⊥ := by
    have hO' : pCoreOf 2 P = ⊥ := by
      by_contra h
      exact hP1 (hBT _ P h (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 P) hPP
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 P))
    exact (Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).mp hO'
  obtain ⟨e⟩ : Nonempty (Bar2 P ≃* alternatingGroup (Fin 5)) := hA5P
  have eP : P ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hO.symm)).trans e
  have hTC : T ⊓ centralizer (P : Set S) = ⊥ := by
    by_contra h
    exact hP1 (hBT _ P h (hT.to_le inf_le_left) hPP
      ((Subgroup.le_centralizer_iff.mp inf_le_right).trans (centralizer_le_normalizer _)))
  let φ : T →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion (hTK.trans hNKP))
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro t ht
    have h1 : P.normalizerMonoidHom (Subgroup.inclusion (hTK.trans hNKP) t) = 1 := ht
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h1
    have h2 : (t : S) ∈ T ⊓ centralizer (P : Set S) := ⟨t.2, h1⟩
    rw [hTC, Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.mpr (Subtype.ext h2)
  have h120 : Nat.card T ∣ 8 * 15 :=
    (Subgroup.card_dvd_of_injective φ hφ).trans
      ((CFSG.RankThree.PartTwo.KFacts.KS166.card_mulAut_of_alt5 eP).trans (by norm_num)).dvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT
  rw [hk] at h120 ⊢
  exact (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 15)).dvd_of_dvd_mul_right h120

theorem a5Normalizer_psu3_two {S : Type} [Group S] [Finite S] {f : ℕ}
    (hS : LieModel S .PSU 3 2 f) (T : Sylow 2 S) {K : Subgroup S} (hA5 : IsAlt (Bar2 K) 5)
    (hT : (T : Subgroup S) ≤ normalizer (K : Set S)) : False := by
  have h8 := card_dvd_eight_of_isAlt_five (fun W X hW hWp hX hXW =>
    CFSG.LocalAnalysis.EvenBN.GMSK.eq_bot_of_isPerfect_of_le_normalizer_of_lieModel_PSU3 hS hWp hW
      (Subgroup.isPerfect_iff.mpr hX) hXW) hA5 T.isPGroup' hT
  rw [T.card_eq_multiplicity,
    CFSG.LocalAnalysis.EvenBN.GMSK.factorization_two_card_of_lieModel_PSU3 hS] at h8
  have h3 : 3 * f ≤ 3 :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
      (h8.trans (by norm_num : (8 : ℕ) = 2 ^ 3).dvd)
  have := CFSG.LocalAnalysis.EvenBN.GMSK.two_le_of_lieModel_PSU3 hS
  omega

theorem kFactShape92A5Normalizer_holds :
    KFactShape92A5Normalizer := by
  intro S _ _ hS K D T hA5 hDK hD hN hT
  have hC : centralizer (D : Set S) ≤ normalizer (K : Set S) :=
    (centralizer_le_normalizer _).trans hN
  rcases hS with ⟨-, h3⟩ | hJ1 | ⟨p, f, hL⟩ | ⟨p, f, hq, hL⟩ | ⟨p, f, hq, hL⟩
  ·
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (h3.to_subgroup K)
    have h2 : 2 ∣ 3 ^ k :=
      hk ▸ (show 2 ∣ 60 by norm_num).trans (sixty_dvd_card_of_isAlt_five hA5)
    exact absurd (Nat.prime_two.dvd_of_dvd_pow h2) (by norm_num)
  ·
    exact Or.inl (a5Normalizer_J1 hJ1 hA5 hD hN)
  ·
    exact Or.inl (a5Normalizer_psl2 hL hA5 hD hN)
  ·
    rcases eq_or_ne p 2 with rfl | hp2
    · exact (not_five_dvd_card_of_lieModel_psl3_two hq hL ((show 5 ∣ 60 by norm_num).trans
        ((sixty_dvd_card_of_isAlt_five hA5).trans (Subgroup.card_subgroup_dvd_card K)))).elim
    · exact Or.inr (a5Normalizer_L3U3_odd hp2 (Or.inl ⟨hq, hL⟩) hA5 hDK hD hC)
  ·
    rcases eq_or_ne p 2 with rfl | hp2
    · exact (a5Normalizer_psu3_two hL T hA5 hT).elim
    · exact Or.inr (a5Normalizer_L3U3_odd hp2 (Or.inr ⟨hq, hL⟩) hA5 hDK hD hC)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09

module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.Lie.SL3Cover
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22S218CenL
import CFSG.LocalAnalysis.UniquenessCase.UC22S218L3
import CFSG.LocalAnalysis.UniquenessCase.UC22S218L3Cov

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem uc22s218n_pRank_le_three_L3_exc (hGA : GriessAllModelsStatement) (D : Data G)
    (Ch : Choice2011 G) (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h211 : S21_1 D Ch)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hX : IsL3 (BarInf L) n)
    (hn : ¬ IsPowTwo n) {p : ℕ} (hp : p ∈ D.sig)
    (hexc : p = 3 ∧ 3 ∣ 2 ^ n - 1 ∧ (3 ∣ n ∨ 3 ∣ Nat.card (Subgroup.center (Bar2 L)))) :
    CFSG.Open.pRank p D.M ≤ 3 := by
  refine uc22s218n_pRank_le_three_of_facts_ex D Ch hSg h614 h211 h76 hH c hL (torusFacts218_L3 hX)
    (fun ℓ hℓ hdvd => ?_) hn hp ?_
  ·
    have h1 : ℓ ∣ Nat.gcd 3 (2 ^ n - 1) := hdvd.trans (card_center_bar2_dvd_of_isL3 hGA hL hX hn)
    have hℓ3 : ℓ = 3 :=
      (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 (h1.trans (Nat.gcd_dvd_left _ _))
    have h3n : 3 ∣ 2 ^ n - 1 := hℓ3 ▸ h1.trans (Nat.gcd_dvd_right _ _)
    subst hℓ3
    exact ⟨fun h => h.2 rfl, fun h => h h3n⟩
  · rintro - - h4 hN s r hs hsn hr hrs -
    obtain ⟨hp3, hp1, -⟩ := hexc
    subst hp3
    have := hN
    have hLM : L ≤ D.M := hL.1.le
    have hr3 : r ≠ 3 := fun h => uc22s218_l3_not_three_dvd hs (by rw [← h]; exact hrs)
    have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd hs.pos hrs
    have : (CFSG.pCore 2 ↥L).Characteristic := CFSG.pCore_characteristic
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hK2 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ¬ ℓ ∣ Nat.card (CFSG.pCore 2 ↥L) := by
      intro ℓ hℓ hℓ2 hdvd
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
      rw [hk] at hdvd
      exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow hdvd))
    have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
    obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
    have hX' : IsL3 (Bar2 L ⧸ Subgroup.center (Bar2 L)) n := LieModel.of_mulEquiv e hX
    have hn0 : 1 ≤ n := (LieModel.admissible hX).2.1
    have hn1 : n ≠ 1 := fun h => hn ⟨0, by simp [h]⟩
    have hn2 : n ≠ 2 := fun h => hn ⟨1, by simp [h]⟩
    obtain ⟨F, _, _, _, α, hF, hα, hαc⟩ := uc22pwI3_exists_cover hq (by omega) hX'
    obtain ⟨E₀, y, hE₀, hE₀c, hyo, hyE, hyZ⟩ := uc22s218_l3_cover_pair_data α hα hαc hr hr3
      (by rw [hF]; exact hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)) (by rw [hF]; exact hp1)
    exact uc22s218_exists_pair_of_kernel hLM (CFSG.pCore 2 ↥L) Nat.prime_three hr (Ne.symm hr3)
      (hK2 3 Nat.prime_three (by norm_num)) (hK2 r hr hr2)
      (uc22s218_l3_pRank_mulAut_le_three_of_quasisimple hq hX') h4 hE₀ hE₀c hyo hyE hyZ

end CFSG.LocalAnalysis.UniquenessCase.UC22

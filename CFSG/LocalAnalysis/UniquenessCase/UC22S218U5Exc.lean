module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Out
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Pair
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5Cov
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5Out
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5Tor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem uc22s218n_pRank_le_three_U5_exc
    (hGA : GriessAllModelsStatement) (D : Data G)
    (Ch : Choice2011 G) (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h211 : S21_1 D Ch)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hX : IsU5 (BarInf L) n)
    (hn : ¬ IsPowTwo n) {p : ℕ} (hp : p ∈ D.sig) (hexc : p = 5 ∧ 5 ∣ 2 ^ n + 1) :
    CFSG.Open.pRank p D.M ≤ 3 := by
  refine uc22s218n_pRank_le_three_of_facts_ex D Ch hSg h614 h211 h76 hH c hL (torusFacts218_U5 hX)
    (fun ℓ hℓ hdvd => ?_) hn hp ?_
  ·
    have h1 : ℓ ∣ Nat.gcd 5 (2 ^ n + 1) := hdvd.trans (card_center_bar2_dvd_of_isU5 hGA hL hX)
    have hℓ5 : ℓ = 5 :=
      (Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).1 (h1.trans (Nat.gcd_dvd_left _ _))
    subst hℓ5
    have hq : 5 ∣ 2 ^ (2 * n) - 1 := by
      have e : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
        rw [two_mul, pow_add]
        simpa using Nat.mul_self_sub_mul_self_eq (2 ^ n) 1
      rw [e]
      exact Dvd.dvd.mul_right hexc.2 _
    exact ⟨fun h => h.2 ⟨rfl, hexc.2⟩, fun h => h hq⟩
  · rintro - - h4 hN s r hs hsn hr hrs -
    obtain ⟨hp5, hp1⟩ := hexc
    subst hp5
    have := hN
    have hLM : L ≤ D.M := hL.1.le
    have hr5 : r ≠ 5 := fun h =>
      ((torusFacts218_U5 hX).tor_of_dvd hs hsn hr hrs).2 ⟨h, hp1⟩
    have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd hs.pos hrs
    have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
    have : (CFSG.pCore 2 ↥L).Characteristic := CFSG.pCore_characteristic
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hK2 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ¬ ℓ ∣ Nat.card (CFSG.pCore 2 ↥L) := by
      intro ℓ hℓ hℓ2 hdvd
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
      rw [hk] at hdvd
      exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow hdvd))
    have h5K : ¬ 5 ∣ Nat.card (CFSG.pCore 2 ↥L) := hK2 5 (by norm_num) (by norm_num)
    have hrK : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥L) := hK2 r hr hr2
    have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
    obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
    have hX' : IsU5 (Bar2 L ⧸ Subgroup.center (Bar2 L)) n := LieModel.of_mulEquiv e hX
    obtain ⟨K, _, h, α, hα, hαc⟩ := uc22s218_u5_exists_cover hq hX'
    by_cases hcase : Function.Injective α ∨ 5 ∣ n
    ·
      obtain ⟨E₀, Q₀, hE₀, hE₀c, hQ₀, hQ₀c, hcomm⟩ :=
        uc22s218_u5_cover_commuting_pair h α hαc hp1 hcase hr hr5 hrn
      exact uc22s218_exists_pair_of_commuting hLM (CFSG.pCore 2 ↥L) (by norm_num) hr
        (Ne.symm hr5) h5K hrK hE₀ hE₀c hQ₀ hQ₀c hcomm
    ·
      obtain ⟨hinj, h5n⟩ := not_or.1 hcase
      have hZ : Subgroup.center (Bar2 L) = ⊥ := uc22s218_u5_center_eq_bot h α hα hαc hp1 hinj
      have hY : IsU5 (Bar2 L) n :=
        LieModel.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hZ).trans
          QuotientGroup.quotientBot) hX'
      obtain ⟨E₀, y, hE₀, hE₀c, hyo, hyE, hyZ⟩ :=
        uc22s218_u5_cover_pair_data h α hαc hp1 hr hr5 hrn
      refine uc22s218_exists_pair_of_outer hLM (CFSG.pCore 2 ↥L) (by norm_num) hr (Ne.symm hr5)
        h5K hrK h4 hE₀ hE₀c hyo hyE hyZ fun V hV hVc => ?_
      obtain ⟨E₁, Q₁, hE₁, hE₁c, hQ₁V, hQ₁, hQ₁c, hact⟩ :=
        uc22s218_u5_outer_pair hY hp1 h5n hr hr5 hrn V hV hVc
      exact ⟨E₁, Q₁, hE₁, hE₁c, hQ₁V, hQ₁, hQ₁c, fun a ha =>
        ⟨1, fun e he => by rw [pow_one]; exact hact a ha e he⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

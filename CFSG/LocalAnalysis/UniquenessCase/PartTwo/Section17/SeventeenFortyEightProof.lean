module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyEightPrimes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFourTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U5TorusRankHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.RankThreeUC.S15

variable {G : Type} [Group G] [Finite G]

theorem seventeen_fortyeight
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h1 : R17_1At D V₀ V hV) (h49 : R17_49At D V₀ V) (hSg : UC6S846.SigmaStd D)
    (h8103 : F08.R8103 D)
    (hK4 : Inputs1719.K_CartanRank)
    (hT : LieOddRankChev) (hN : uc22p20rNativeGriess) :
    R17_48At D V₀ V := by
  have hK3 : Inputs1719.K_BorelTorusAbelian := Inputs1719.k_BorelTorusAbelian_holds
  classical
  have hK8a : Inputs1719.K_U5TorusRank := Inputs1719.k_U5TorusRank_holds
  intro L X p n l C Dc Gamma ctx hU5
  have hprime : ∀ s : ℕ, s.Prime → s ∣ 2 ^ n + 1 → s = 5 := by
    intro s hs hsdvd
    exact (Ctx17_42.u5_exceptional_of_prime ctx h1 h49 hSg hK3 hK8a hT hN hU5 hs hsdvd).1
  have hgt : 1 < 2 ^ n + 1 := by
    have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
    omega
  obtain ⟨s, hs, hsdvd⟩ := Nat.exists_prime_and_dvd (by omega : 2 ^ n + 1 ≠ 1)
  have h25 : ¬ 25 ∣ 2 ^ n + 1 :=
    (Ctx17_42.u5_exceptional_of_prime ctx h1 h49 hSg hK3 hK8a hT hN hU5 hs hsdvd).2.2
  have hZ1 : Nat.card (Subgroup.center (Bar2 L)) = 1 :=
    (Ctx17_42.u5_exceptional_of_prime ctx h1 h49 hSg hK3 hK8a hT hN hU5 hs hsdvd).2.1
  let k := (2 ^ n + 1).primeFactorsList.length
  have hpow : 2 ^ n + 1 = 5 ^ k :=
    Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (fun {d} hd hdd => hprime d hd hdd)
  have hk1 : k = 1 := by
    have hkpos : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero] at hpow
      omega
    by_contra hne
    have hk2 : 2 ≤ k := by omega
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk2
    have h25' : 25 ∣ 5 ^ k := by
      rw [hj, pow_add]
      exact ⟨5 ^ j, by norm_num⟩
    exact h25 (hpow ▸ h25')
  have hn2 : n = 2 := by
    have h5 : 2 ^ n + 1 = 5 := by simpa [hk1] using hpow
    have h4 : 2 ^ n = 4 := by omega
    exact Nat.pow_right_injective (le_refl 2) (by simpa using h4)
  have hU5' : IsU5 (BarInf L) 2 := by simpa [hn2] using hU5
  have hZbot : Subgroup.center (Bar2 L) = ⊥ := Subgroup.card_eq_one.mp hZ1
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot ctx.mem_calC.2.2 hZbot
  have hU5bar2 : IsU5 (Bar2 L) 2 := LieModel.of_mulEquiv e hU5'
  have hC3 : 2 ≤ CFSG.Open.pRank 3 C := by
    have h := cartanRank_le_pRank_cartan hK4 ctx.mem_calC ctx.cartan hU5'.admissible hU5'
      Nat.prime_three (by norm_num) (by norm_num) (fun h => by cases h) (fun h => by cases h)
    have hrank : CS17LieRank .PSU 5 = 2 := by norm_num [CS17LieRank]
    simpa [hrank] using h
  have hDc3 : 2 ≤ CFSG.Open.pRank 3 Dc :=
    hC3.trans (pRank_cartan_le_pRank_Dc ctx Nat.prime_three)
  have hnotstr : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    intro hstr
    have hk : D.k = 1 := Data.k_eq_one_of_isStronglyPEmbedded D hstr
    have hle : CFSG.Open.pRank 3 Dc ≤ 1 := pRank_three_Dc_le_one_of_k_one ctx hK3 h1 hk
    omega
  have hk2 : D.k = 2 := (Data.k_eq_two_iff D).mpr hnotstr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf (G := G) 3 L
  have h8102 : F08.Hyp8102 D L P p 2 :=
    ⟨ctx.mem_calC, Or.inl ⟨hU5bar2, rfl⟩, hnotstr, ctx.p_mem, hP⟩
  have h8103' := h8103 L P p 2 h8102
  have hcong : ((2 : ℤ) ^ 2 ≡ -1 [ZMOD (p : ℤ)]) := h8103'.2.1.1
  have he : evenRank G = 3 := h8103'.2.1.2
  have hp5 : p = 5 := by
    have hdvd : (p : ℤ) ∣ (5 : ℤ) := by
      simpa using (Int.ModEq.dvd hcong).neg_right
    have hdvd5 : p ∣ 5 := by exact_mod_cast hdvd
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd5 with h1p | h5p
    · exact absurd h1p (D.sig_prime p ctx.p_mem).1.ne_one
    · exact h5p
  have hXL : L = X := h49 L X p n l C Dc Gamma ctx
  have hU5X : IsU5 (Bar2 X) 2 := hXL ▸ hU5bar2
  have hP3 : P17_42_3 D X p := p17_42_three_of_isU5_two hU5X hk2 hp5 he
  exact ctx.counter (Or.inr (Or.inr (Or.inl hP3)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

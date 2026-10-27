module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PTwo
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3P149
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PAut
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PInv
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22S213L3Cover
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
import CFSG.LocalAnalysis.UniquenessCase.UC22P20zbb
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.Quasithin.Background.A3FactsA134
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34LFDefs
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_12aFR34L3PRes (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch,
    (∃ b ∈ c.B0, b ∈ normalizer (D.T : Set G) ∧ (orderOf b).Prime ∧ 5 ≤ orderOf b) →
    ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 →
      (LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1) →
      (∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f) →
      (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → F08.Thin8 L

theorem uc22s2112l3p_of_inputs (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G}
    (hSig : UC6S846.SigmaStd D) (hKF7 : KF7Use D) (h5 : S21_5 D Ch) (h149 : R149L3P D) :
    S21_12aFR34L3PRes D Ch := by
  classical
  rintro hH c ⟨b, hbB, hbT, hbp, hb5⟩ L hL p hp hp2 hX - hfaith
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hb : b ∈ normalizer (L : Set G) :=
    h5 hH { c with B := c.B0, hB := c.hB0, hle := le_rfl } L hL hbB
  have hθ : inducedBarInfAutHom L ⟨b, hb⟩ ≠ 1 := fun h1 => by
    have hb1 := hfaith b hbB (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 hb h1)
    rw [hb1, orderOf_one] at hbp
    exact Nat.not_prime_one hbp
  obtain ⟨hbN, hcomm, x, hx, S, hxS⟩ := uc22s2112l3p_conj hGA hL hp2 hX hb hbT hbp hb5 hθ
  have hinj : Function.Injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ center (BarInf L) := by
      rw [mem_center_iff]
      intro w
      have h := congrArg (fun φ : MulAut (BarInf L) => φ w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc w * z = z * w * z⁻¹ * z := by rw [h]
        _ = z * w := by group
    rwa [center_barInf_eq_bot hL.2.2, mem_bot] at hzc
  have hxs : orderOf x = orderOf b := by
    rw [← orderOf_injective _ hinj x, ← hx]
    have hd := orderOf_map_dvd (inducedBarInfAutHom L) ⟨b, hb⟩
    rw [Subgroup.orderOf_mk] at hd
    rcases (Nat.dvd_prime hbp).1 hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hθ
    · exact h1
  have hxp : (orderOf x).Prime := hxs ▸ hbp
  have hsd : orderOf b ∣ p ^ 2 - 1 := by
    rw [← hxs]
    exact uc22s2112l3p_dvd_sq_sub_one hp2 hX S hxS hxp
  have hp11 : 11 ≤ p := by
    by_contra hlt
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    have hodd := hp.eq_two_or_odd
    have h9 : p ≠ 9 := fun h => by
      subst h
      exact absurd (hp.eq_one_or_self_of_dvd 3 ⟨3, rfl⟩) (by omega)
    have h48 : p ^ 2 - 1 ∣ 2 ^ 4 * 3 := by
      rcases (by omega : p = 3 ∨ p = 5 ∨ p = 7) with rfl | rfl | rfl <;> norm_num
    rcases (Nat.Prime.dvd_mul hbp).1 (hsd.trans h48) with h | h
    · have := Nat.le_of_dvd (by norm_num) (hbp.dvd_of_dvd_pow h)
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega
  obtain ⟨Y, hYC, ⟨eY⟩⟩ := uc22s2112l3p_exists_sl2_le_centralizer hp2 hX S hxS
  have hY : Y ≤ signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩) := fun y hy => by
    show inducedBarInfAutHom L ⟨b, hb⟩ y = y
    rw [hx, MulAut.conj_apply, ← mem_centralizer_singleton_iff.1 (hYC hy), mul_inv_cancel_right]
  obtain ⟨t, htM, ht2, ht⟩ :=
    uc22s2112l3p_exists_inv h149 hH c hL hp hp2 (by omega) hX hbB hb hbp hbN hY eY
  have hZ : ¬ p ∣ Nat.card (center (Bar2 L)) := by
    rcases hX with h | h
    · exact uc22s213_not_dvd_card_center_of_rank_three_odd hGA hL (.inl rfl) hp2 h
    · exact uc22s213_not_dvd_card_center_of_rank_three_odd hGA hL (.inr rfl) hp2 h
  have hpL : 2 ≤ Open.pRank p L := by
    rw [← uc22s213_pRank_barInf_of_prime hL.2.2 hp hp2 hZ]
    exact CFSG.Quasithin.A3Facts.two_le_pRank_psl_psu_three hp2
      (hX.imp (·.statedClassicalModel_of_ne_zero (by norm_num))
        (·.statedClassicalModel_of_ne_zero (by norm_num)))
  obtain ⟨hTN, htN⟩ := uc22s2112l3p_normalizes hSig hKF7 h5 hH c hL hp hp11 hZ hpL hbB hb hbT hbp
    hb5 hbN hcomm hY eY htM ht
  exact uc22s2112l3p_false_of_inv hb hbp hb5 hθ hTN hcomm ht2 htN ht

theorem uc22s2112l3p_of_not_two_pow {D : Data G} {Ch : Choice2011 G}
    (h : S21_12aFR34L3PRes D Ch) :
    H1930 D → ∀ c : Ctx21 D Ch, c.n ≠ 0 → ¬ IsPowTwo c.n →
      ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 →
        (LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1) →
        (∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f) →
        (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → F08.Thin8 L := by
  intro hH c hn0 hn2
  obtain ⟨e, m, hm, hko⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  obtain ⟨k, hk⟩ := id hm
  have hm3 : 3 ≤ m := by
    rcases k with _ | k
    · exact absurd ⟨e, by rw [hko, hk]; simp⟩ hn2
    · omega
  have h4 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2m : 2 ^ m = 2 * 4 ^ k := by
    rw [hk, pow_succ, pow_mul, mul_comm]
    norm_num
  have h8 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  obtain ⟨s, hs, hsd⟩ := Nat.exists_prime_and_dvd (show 2 ^ m - 1 ≠ 1 by omega)
  have hs5 : 5 ≤ s := by
    refine hs.five_le_of_ne_two_of_ne_three ?_ ?_ <;> rintro rfl <;> omega
  have hmn : 2 ^ m - 1 ∣ 2 ^ c.n - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (2 ^ m) 1 (2 ^ e)
    rwa [one_pow, ← pow_mul, mul_comm m, ← hko] at h
  have hsB : s ∈ piSet c.B0 := by
    rw [c.hpi]
    exact ⟨hs, hsd.trans hmn⟩
  obtain ⟨b, hbB, hbs⟩ := uc22p22i_exists_elt_of_mem_piSet hsB
  have hbα : b ∈ oPi {q | q.Prime ∧ q ∣ 2 ^ m - 1} c.B0 :=
    uc22pwtb_mem_oPi c.hB0.2.1 hbB fun q hq hqd => by
      rw [hbs] at hqd
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq hs).1 hqd
      exact ⟨hq, hsd⟩
  exact h hH c ⟨b, hbB, c.hα e m hm hko hbα, hbs ▸ hs, hbs ▸ hs5⟩

theorem s21_12aFR34L3P_of_res_two {D : Data G} {Ch : Choice2011 G}
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (hR : S21_12aFR34L3PRes D Ch)
    (h2 : S21_12aFR34L3PTwo D Ch) : S21_12aFR34L3P D Ch := by
  intro hH c
  by_cases hpow : IsPowTwo c.n
  · exact h2 hH c (hn3 hH c) hpow
  · exact uc22s2112l3p_of_not_two_pow hR hH c (by have := hn3 hH c; omega) hpow

theorem uc22s2112l3p_setup4 (hGA : GriessAllModelsStatement)
    (hK35w : UCK.K35w) (hKZ : PartOne.Section8.StronglyEmbeddedCentralFree) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M)
    (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree) (hB : BadNoStrongThree)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) {Ch : Choice2011 G}
    (hKF7 : KF7Use (UC6.dataOfSetup4 hS hU S)) (h5 : S21_5 (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_12aFR34L3PRes (UC6.dataOfSetup4 hS hU S) Ch :=
  uc22s2112l3p_of_inputs hGA (UC6S846.sigmaStd_dataOfSetup4 hS hU S) hKF7 h5
    (uc22s2112l3p_r149_setup4 hGA hK35w hKZ hS hU S hσ hPart hSE hK3 hB hOut)

end CFSG.LocalAnalysis.UniquenessCase.UC22

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixO2Rest
public import CFSG.GroupTheory.SL2CardDivisibility
public import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterHolds
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwG2D4
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main
public import CFSG.GroupTheory.CentralKernelOddDivisor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open scoped MatrixGroups
open CFSG.ClassicalInvolution.ModelFacts
open CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
open CFSG.LieType.Steinberg.TwistedD4
open CFSG.GroupTheory (dvd_card_sl2_of_dvd_mul_sq_sub_one
  dvd_card_sl2_cube_of_dvd_mul_sq_sub_one dvd_card_map_of_ker_le_center)

theorem K_G176L2RankThree_holds : K_G176L2RankThree := by
  intro X _ _ f hf hL2
  obtain ⟨r, f0, hr, hr2, hq, hf0, hm⟩ := hL2
  have hr3 : r = 3 := by
    have hdvd : r ∣ 3 ^ f := by rw [hq]; exact dvd_pow_self r (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hr.dvd_of_dvd_pow hdvd)
  subst hr3
  have hf0f : f0 = f := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 3)
    exact hq.symm
  subst f0
  have hm' : CFSG.Open.StatedClassicalModel X .PSL 2 3 f :=
    CFSG.Blueprint.LieModel.statedClassicalModel hm (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨-, K, hfield, hfinite, hKcard, ⟨e⟩⟩ := hm'
  let eX : X ≃* PSL(2, GaloisField 3 f) :=
    e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 3 f (by omega) hKcard)
  have hle := CFSG.Quasithin.H13.S3320.le_pRank_of_psl2 (p := 3) (f := f) (by omega) eX
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hle
  omega

section Certificates


theorem K_G176FunOrder_holds : K_G176FunOrder := by
  intro X _ _ q r Kb hK hr hr2 hrq
  obtain ⟨t, n, p0, e, hp0, hp02, hq, hfund, hadm, ψ, hsurj, hker, R, hR, rfl⟩ := hK
  have : Fact (Nat.Prime p0) := ⟨hp0⟩
  have he : 1 ≤ e := hadm.2.1
  let R' : Subgroup (modelUniv t n p0 e hp0).K := R
  have hR' : R' ∈ fundamentalSubgroups t (modelUniv t n p0 e hp0).D := hR
  by_cases hG2 : t = .G2
  · subst hG2
    obtain ⟨g, γ, hγ, hReq⟩ := mem_roots_of_mem_fundamentalSubgroups hR'
    obtain ⟨w, i, rfl⟩ : ∃ (w : (CFSG.LieType.RootSystem.coxeterMatrix
        (modelUniv .G2 n p0 e hp0).D.isFiniteType).Group)
        (i : Fin (modelUniv .G2 n p0 e hp0).D.rank),
        γ = CFSG.LieType.RootSystem.weylAction
          (modelUniv .G2 n p0 e hp0).D.isFiniteType w (Pi.single i 1) := by
      rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
      · exact ⟨w, i, rfl⟩
      · rw [show (modelUniv .G2 n p0 e hp0).D.divisible = ∅ from rfl] at hi
        exact absurd hi (Set.notMem_empty i)
    obtain ⟨_, _, hct, -⟩ := hasBruhatDatum .G2 n p0 e hp0 trivial hadm
    obtain ⟨g', hg'⟩ := exists_map_conj_rankOne hct w
    have h1 := hg' (Pi.single i 1) (Or.inl ⟨1, i, by simp⟩)
    have hReq2 : R' = ((rankOne (modelUniv .G2 n p0 e hp0).D.rootGroup i).map
        (MulAut.conj (g * g')).toMonoidHom) := by
      rw [hReq, ← h1, CFSG.LieType.Chevalley.map_conj_map_conj]
      rfl
    obtain ⟨e0⟩ := g2_rankOne_equiv (K := GaloisField p0 e) i
    have eR : R' ≃* SL(2, GaloisField p0 e) :=
      (hReq2.symm ▸ subgroupMapConjEquiv _ (g * g')).trans e0
    have hrq' : r ∣ p0 ^ e * ((p0 ^ e) ^ 2 - 1) := by
      rwa [hq] at hrq
    have hcardR : r ∣ Nat.card R' := by
      rw [Nat.card_congr eR.toEquiv]
      exact dvd_card_sl2_of_dvd_mul_sq_sub_one (F := GaloisField p0 e) (q := p0 ^ e)
        (GaloisField.card p0 e (by omega)) hrq'
    have : Finite R' := Finite.of_equiv _ eR.symm.toEquiv
    exact dvd_card_map_of_ker_le_center (R := R') hker
      (fun c hc hcc => fundCentral_sq_of_equiv_sl2 eR hc hcc) hr hr2 hcardR
  · by_cases hD4 : t = .trialityD4
    · subst hD4
      have hK' : Nat.card (GaloisField p0 (3 * e)) = (p0 ^ e) ^ 3 := by
        rw [GaloisField.card p0 (3 * e) (by omega), pow_mul']
      have hσ := sigma_three_of_card
        (σ := iterateFrobenius (GaloisField p0 (3 * e)) p0 e) (q := p0 ^ e) hK'
        (fun c => iterateFrobenius_def p0 e c)
      obtain ⟨g, γ, hγ, hReq⟩ := mem_roots_of_mem_fundamentalSubgroups hR'
      obtain ⟨w, i, rfl⟩ : ∃ (w : (CFSG.LieType.RootSystem.coxeterMatrix
          (modelUniv .trialityD4 n p0 e hp0).D.isFiniteType).Group)
          (i : Fin (modelUniv .trialityD4 n p0 e hp0).D.rank),
          γ = CFSG.LieType.RootSystem.weylAction
            (modelUniv .trialityD4 n p0 e hp0).D.isFiniteType w (Pi.single i 1) := by
        rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
        · exact ⟨w, i, rfl⟩
        · rw [show (modelUniv .trialityD4 n p0 e hp0).D.divisible = ∅ from rfl] at hi
          exact absurd hi (Set.notMem_empty i)
      obtain ⟨_, _, hct, -⟩ := hasBruhatDatum .trialityD4 n p0 e hp0 trivial hadm
      obtain ⟨g', hg'⟩ := exists_map_conj_rankOne hct w
      have h1 := hg' (Pi.single i 1) (Or.inl ⟨1, i, by simp⟩)
      have hReq2 : R' = ((rankOne (modelUniv .trialityD4 n p0 e hp0).D.rootGroup i).map
          (MulAut.conj (g * g')).toMonoidHom) := by
        rw [hReq, ← h1, CFSG.LieType.Chevalley.map_conj_map_conj]
        rfl
      have hrq' : r ∣ p0 ^ e * ((p0 ^ e) ^ 2 - 1) := by
        rwa [hq] at hrq
      match i with
      | ⟨0, _⟩ =>
          have e0 : (rankOne (modelUniv .trialityD4 n p0 e hp0).D.rootGroup
              (show Fin (modelUniv .trialityD4 n p0 e hp0).D.rank from ng 0)) ≃*
                SL(2, fixedField (iterateFrobenius (GaloisField p0 (3 * e)) p0 e)) :=
            (MulEquiv.subgroupCongr (rankOne_long_eq_range hσ)).trans
              (MonoidHom.ofInjective (slLong_injective hσ)).symm
          have eR : R' ≃* SL(2, fixedField
              (iterateFrobenius (GaloisField p0 (3 * e)) p0 e)) :=
            (hReq2.symm ▸ subgroupMapConjEquiv _ (g * g')).trans e0
          have hcardR : r ∣ Nat.card R' := by
            rw [Nat.card_congr eR.toEquiv]
            exact dvd_card_sl2_of_dvd_mul_sq_sub_one (F := fixedField
              (iterateFrobenius (GaloisField p0 (3 * e)) p0 e)) (q := p0 ^ e)
              (card_fixedField_iterateFrobenius he) hrq'
          have : Finite R' := Finite.of_equiv _ eR.symm.toEquiv
          exact dvd_card_map_of_ker_le_center (R := R') hker
            (fun c hc hcc => fundCentral_sq_of_equiv_sl2 eR hc hcc) hr hr2 hcardR
      | ⟨1, _⟩ =>
          have e0 : (rankOne (modelUniv .trialityD4 n p0 e hp0).D.rootGroup
              (show Fin (modelUniv .trialityD4 n p0 e hp0).D.rank from ng 1)) ≃*
                SL(2, GaloisField p0 (3 * e)) :=
            (MulEquiv.subgroupCongr (rankOne_short_eq_range hσ)).trans
              (MonoidHom.ofInjective (slShort_injective hσ)).symm
          have eR : R' ≃* SL(2, GaloisField p0 (3 * e)) :=
            (hReq2.symm ▸ subgroupMapConjEquiv _ (g * g')).trans e0
          have hcardR : r ∣ Nat.card R' := by
            rw [Nat.card_congr eR.toEquiv]
            exact dvd_card_sl2_cube_of_dvd_mul_sq_sub_one (F := GaloisField p0 (3 * e))
              hK' hrq'
          have : Finite R' := Finite.of_equiv _ eR.symm.toEquiv
          exact dvd_card_map_of_ker_le_center (R := R') hker
            (fun c hc hcc => fundCentral_sq_of_equiv_sl2 eR hc hcc) hr hr2 hcardR
    · obtain ⟨eR⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp02 hfund hadm
        hG2 hD4 hR
      have eR' : R' ≃* SL(2, GaloisField p0 e) := eR
      have hrq' : r ∣ p0 ^ e * ((p0 ^ e) ^ 2 - 1) := by
        rwa [hq] at hrq
      have hcardR : r ∣ Nat.card R' := by
        rw [Nat.card_congr eR'.toEquiv]
        exact dvd_card_sl2_of_dvd_mul_sq_sub_one (F := GaloisField p0 e) (q := p0 ^ e)
          (GaloisField.card p0 e (by omega)) hrq'
      have : Finite R' := Finite.of_equiv _ eR'.symm.toEquiv
      exact dvd_card_map_of_ker_le_center (R := R') hker
        (fun c hc hcc => fundCentral_sq_of_equiv_sl2 eR' hc hcc) hr hr2 hcardR

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

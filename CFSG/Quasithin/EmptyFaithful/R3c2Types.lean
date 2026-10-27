module

public import CFSG.Quasithin.EmptyFaithful.R3c2Excl
public import CFSG.Quasithin.EmptyFaithful.Insp9Tr
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Background.FFC4G2
public import CFSG.Quasithin.Background.P3G2Iso
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
import CFSG.Open.StatedZModTwo
public import CFSG.Quasithin.EmptyFaithful.R3cSL2

public section

namespace CFSG.Quasithin.R3c2

open CFSG.Quasithin CFSG.Quasithin.Vol2 CFSG.Assembly.LowTwoRank

theorem pRank_three_statedSL_two {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSL 2 K)) = 1 := by
  refine le_antisymm (R3c.pRank_three_le_one_of_noElemNine (R3c.noElemNine_statedSL_two hK))
    (R3c.one_le_pRank_three_of_dvd ?_)
  rw [R3c.card_statedSL_two_pow hK]
  have h4 : 4 ^ n % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have : 3 ∣ 4 ^ n - 1 := by omega
  exact Dvd.dvd.mul_left this _

theorem isPSL_two_of_statedSL {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    (e : X ≃* ↥(StatedSL n (ZMod 2))) : IsPSL n 2 1 X :=
  CFSG.Open.StatedAPI.statedClassicalModel_psl_of_mulEquiv_statedSL_zmod_two hn e

theorem isSimpleGroup_of_quasisimple_of_center_eq_bot {X : Type*} [Group X]
    (hq : CFSG.IsQuasisimple X) (hc : Subgroup.center X = ⊥) : IsSimpleGroup X := by
  have := hq.2.1
  exact ((QuotientGroup.quotientBot (G := X)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hc.symm)).isSimpleGroup

theorem not_isQuasisimple_statedSp_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {X : Type} [Group X] (e : X ≃* ↥(StatedSp 2 K)) : ¬ CFSG.IsQuasisimple X := by
  intro hq
  have : Group.IsPerfect X := hq.1
  have hperf : commutator ↥(StatedSp 2 K) = ⊤ :=
    Group.isPerfect_def.1 (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
  have h1 : Nat.card ↥(commutator ↥(StatedSp 2 K)) = 360 := by
    rw [Nat.card_congr (CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hK).toEquiv,
      card_alternatingGroup_six]
  have h2 : Nat.card ↥(StatedSp 2 K) = 720 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK,
      show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
    norm_num
  rw [hperf, Subgroup.card_top, h2] at h1
  omega

theorem not_isQuasisimple_quasithinG2_two
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {X : Type} [Group X] (e : X ≃* ↥(CFSG.Open.quasithinG2 K)) :
    ¬ CFSG.IsQuasisimple X := by
  intro hq
  have : Group.IsPerfect X := hq.1
  have hperf : ⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ = CFSG.Open.quasithinG2 K :=
    Subgroup.isPerfect_iff.1 (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
  have h1 : Nat.card ↥(CFSG.Open.quasithinG2 K) = 12096 := by
    rw [card_quasithinG2_1527d (n := 1) (by simpa using hK), hK]
    norm_num
  have hGF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero]
    norm_num
  have h2 : Nat.card ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ = 6048 := by
    rw [Nat.card_congr ((Insp9.g2DerivedEquivZMod2 K hK).trans
      (Insp9.g2DerivedEquivZMod2 (GaloisField 2 1) hGF).symm).toEquiv]
    exact CFSG.Quasithin.G11.P3G2.card_commutatorG2
  rw [hperf, h1] at h2
  omega

theorem one_le_of_natCard_eq_two_pow {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := Finite.one_lt_card_iff_nontrivial.2 (inferInstance : Nontrivial K)
    simp [hK] at this
  · exact hn

theorem exclusion_sp4 (hE : Ch11.SecA.FactA318Excl) {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) {X : Type} [Group X] [Finite X] (e : X ≃* ↥(StatedSp 2 K))
    (hq : CFSG.IsQuasisimple X) : A318Exclusion X := by
  have hn : 2 ≤ n := by
    by_contra hn
    have h1 := one_le_of_natCard_eq_two_pow hK
    obtain rfl : n = 1 := by omega
    exact not_isQuasisimple_statedSp_two (by simpa using hK) e hq
  obtain ⟨hz, -, hno⟩ := hE.1 K n hn hK
  have hXc : Subgroup.center X = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [hz] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hXs := isSimpleGroup_of_quasisimple_of_center_eq_bot hq hXc
  refine ⟨hXs, ((FFC.threeRank2_statedSp (K := K)).of_mulEquiv e.symm).pRank_two_le, ?_⟩
  intro Y _ s p k hp hk hY hmod f hf
  exact ((hno Y s p k hY).1 (e.toMonoidHom.comp f) (e.surjective.comp hf))

theorem exclusion_g2
    (hE : Ch11.SecA.FactA318Excl) {n : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ n) {X : Type} [Group X] [Finite X]
    (e : X ≃* ↥(CFSG.Open.quasithinG2 K)) (hq : CFSG.IsQuasisimple X) : A318Exclusion X := by
  have hn : 2 ≤ n := by
    by_contra hn
    have h1 := one_le_of_natCard_eq_two_pow hK
    obtain rfl : n = 1 := by omega
    exact not_isQuasisimple_quasithinG2_two (by simpa using hK) e hq
  have : Group.IsPerfect X := hq.1
  have hperf : ⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ = CFSG.Open.quasithinG2 K :=
    Subgroup.isPerfect_iff.1 (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
  set e' : X ≃* ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
    e.trans (MulEquiv.subgroupCongr hperf.symm) with he'
  obtain ⟨-, hz, hno⟩ := hE.1 K n hn hK
  have hXc : Subgroup.center X = ⊥ := by
    have h1 := Subgroup.map_center_eq e'
    rw [hz] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e'.injective).mp h1
  have hXs := isSimpleGroup_of_quasisimple_of_center_eq_bot hq hXc
  have := R3c.charP_two_of_natCard_eq_two_pow hK
  refine ⟨hXs, ((FFC.threeRank2_g2 K).of_mulEquiv e.symm).pRank_two_le, ?_⟩
  intro Y _ s p k hp hk hY hmod f hf
  exact ((hno Y s p k hY).2 (e'.toMonoidHom.comp f) (e'.surjective.comp hf))

theorem exclusion_g2Derived
    (hK : KnownFacts15122Types) {K : Type} [Field K] [Finite K]
    (h2 : Nat.card K = 2) {X : Type} [Group X] [Finite X]
    (e : X ≃* ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆) : A318Exclusion X := by
  have hGF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero]
    norm_num
  set e' : X ≃* ↥(StatedSU 3 3 CFSG.Quasithin.G2U.F9) :=
    e.trans ((Insp9.g2DerivedEquivZMod2 K h2).trans
      ((Insp9.g2DerivedEquivZMod2 (GaloisField 2 1) hGF).symm.trans
        CFSG.Quasithin.G11.P3G2.commutatorG2EquivSU)) with he'
  refine hK.u33 X ?_
  obtain ⟨hadm, K', _, _, hKc, ⟨φ⟩⟩ := CFSG.LinearGroups.UnitaryThreeOverNine.classicalModel_statedSU
    (F := CFSG.Quasithin.G2U.F9) CFSG.Quasithin.G2U.card_F9
  exact ⟨hadm, K', inferInstance, inferInstance, hKc, ⟨e'.trans φ⟩⟩

end CFSG.Quasithin.R3c2

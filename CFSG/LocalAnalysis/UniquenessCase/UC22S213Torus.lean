module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Prime
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63G2Sylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63D4Sylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63F4Sylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63LieOut
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63J2Tits
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECArith
import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinCycB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSG.LieType.SteinbergBRMulEquivCores
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Config

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (exceptionalOrders)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvable StronglyEmbeddedThree BadNoStrongThree)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3ClosedTorus (L : Subgroup G) : Prop :=
  LieModel (BarInf L) .Tits 0 2 1 ∨
    ∃ r p f : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ p ^ f - 1 ∧ ¬ r ∣ f ∧
      (LieModel (BarInf L) .G2 0 p f ∨ (p = 2 ∧ LieModel (BarInf L) .trialityD4 0 p f) ∨
        (p = 2 ∧ LieModel (BarInf L) .twistedF4 0 p f))

section Torus

set_option linter.unusedSectionVars false


private theorem uc22s213_g2_rank_sylow {X : Type} [Group X] [Finite X] {p f r : ℕ}
    (h : LieModel X .G2 0 p f) (hr : r.Prime) (hr3 : 3 < r) (hrd : r ∣ p ^ f - 1) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) ∧
      ∀ P : Sylow r X, IsMulCommutative (P : Subgroup X) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2
    (h.chevalleyExceptionalModel (by decide)).2
  haveI := Finite.of_equiv X e.toEquiv
  obtain ⟨h2, hab⟩ := PartOne.Section8.two_le_pRank_and_sylow_abelian_adjointGroup_G2 hr hr3
    (by rw [hK]; exact hrd)
  refine ⟨(CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e).symm ▸ h2, fun P => ?_⟩
  obtain ⟨Q⟩ : Nonempty (Sylow r (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) := inferInstance
  obtain ⟨eQ⟩ := CFSG.GroupTheory.WeirSylow.nonempty_sylow_mulEquiv_sylow_of_mulEquiv e Q P
  haveI := hab Q
  exact IsMulCommutative.of_comm fun x y => eQ.symm.injective (by
    rw [map_mul, map_mul]
    exact mul_comm' _ _)

theorem uc22s213_not_centralizesBar_of_torus (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive)
    (hSS : StronglyEmbeddedSolvable) (hK3 : StronglyEmbeddedThree) (hB : BadNoStrongThree)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) (Ch : Choice2011 G)
    (hH : H1930 (UC6.dataOfSetup4 hS hU S)) (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch)
    {L : Subgroup G} (hL : L ∈ calC S.M) (hT : S21_3ClosedTorus L) {a : G} (ha : a ∈ c.B)
    (hpr : (orderOf a).Prime)
    (hN : ∀ p ∈ uniqueFourSigma S.M,
      CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  have key : ∀ {r : ℕ}, r.Prime → 5 ≤ r → center (Bar2 L) = ⊥ →
      2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (BarInf L)) →
      (∀ P : Sylow r (BarInf L), IsMulCommutative (P : Subgroup (BarInf L))) →
      ¬ r ∣ Nat.card (Outer (BarInf L)) → 3600 < Nat.card (BarInf L) →
      ¬ CentralizesBar a L := fun hr hr5 hZ h2 hab hout h3600 =>
    uc22s213_not_centralizesBar_of_prime hS hU S hσ hPart hSE hSS hK3 hB hOut Ch hH c hL hr hr5
      (by rw [hZ, card_bot]; exact hr.not_dvd_one) h2 hab hout h3600 ha hpr hN
  rcases hT with hX | ⟨r, p, f, hr, hr5, hrd, hrf, hX | ⟨rfl, hX⟩ | ⟨rfl, hX⟩⟩
  ·
    have hcard : Nat.card (BarInf L) = 17971200 :=
      CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover.card_tits hX
    have h53 : ¬ 5 ^ 3 ∣ Nat.card (BarInf L) := by
      rw [hcard]
      norm_num
    refine key Nat.prime_five le_rfl
      (center_bar2_eq_bot_of_row hL (t := .Tits) (n := 0) (p := 2) (f := 1) rfl rfl
        (CFSG.LieType.Steinberg.CentralExt.GriessNative.tits_row hX))
      (PartOne.Section8.pRank_five_eq_two_of_lieModel_tits hX).ge
      (fun P => ⟨⟨fun x y => Subtype.ext
        (CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinCyc.comm_of_not_dvd Nat.prime_five
          P.isPGroup' h53 x x.2 y y.2)⟩⟩)
      (PartOne.Section8.not_five_dvd_card_outer_of_lieModel_tits hX) ?_
    rw [hcard]
    norm_num
  ·
    obtain ⟨hp, hf, -⟩ := hX.admissible
    have hq1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
    have hrq : r ≤ p ^ f - 1 := Nat.le_of_dvd (by omega) hrd
    have hq6 : 6 ≤ p ^ f := by omega
    obtain ⟨h2, hab⟩ := uc22s213_g2_rank_sylow hX hr (by omega) hrd
    have hc := CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover.card_of_lieModel hX
    simp only [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator,
      CFSG.ComponentClassification.CatLeaf.lieOrderDivisor, mul_one] at hc
    refine key hr hr5 ?_ h2 hab
      (PartOne.Section8.not_dvd_card_outer_lieModel_G2 hX hp hr (by omega) hrd hrf) ?_
    · refine center_bar2_eq_bot_of_row hL (t := .G2) (n := 0) (p := p) (f := f) rfl ?_
        (CFSG.LieType.Steinberg.CentralExt.GriessNative.g2_row
          (CFSG.LieType.Steinberg.CentralExt.GriessNative.chevalley_of_lieModel hX
            (by decide)).2 (by omega))
      have h22 : ¬ (p = 2 ∧ f = 2) := by
        rintro ⟨rfl, rfl⟩
        norm_num at hq6
      have h31 : ¬ (p = 3 ∧ f = 1) := by
        rintro ⟨rfl, rfl⟩
        norm_num at hq6
      unfold exceptionalOrders
      split <;> simp_all
    · rw [hc]
      have h6 : 3600 < (p ^ f) ^ 6 :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_left hq6 6)
      have h2' : 0 < (p ^ f) ^ 2 - 1 :=
        Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) hq1)
      exact lt_of_lt_of_le h6 ((Nat.le_mul_of_pos_right _ (by omega)).trans
        (Nat.le_mul_of_pos_right _ h2'))
  ·
    obtain ⟨hab, h2⟩ :=
      PartOne.Section8.exists_sylow_abelian_of_lieModel_trialityD4 hX hr (by omega) hrd
    have hf : 1 ≤ f := hX.admissible.2.1
    have hq1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    have hq2 : 2 ≤ 2 ^ f := hq1
    have hc := CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover.card_of_lieModel hX
    simp only [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator,
      CFSG.ComponentClassification.CatLeaf.lieOrderDivisor, mul_one] at hc
    refine key hr hr5 (center_bar2_eq_bot_of_is3D4 hL hX) h2 hab
      (PartOne.Section8.not_dvd_card_outer_lieModel_trialityD4 hX Nat.prime_two hr (by omega)
        hrd hrf) ?_
    rw [hc]
    have h12 : 3600 < (2 ^ f) ^ 12 :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_left hq2 12)
    have h6 : 0 < (2 ^ f) ^ 6 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) hq1)
    have h2' : 0 < (2 ^ f) ^ 2 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) hq1)
    exact lt_of_lt_of_le h12 (((Nat.le_mul_of_pos_right _ (by positivity)).trans
      (Nat.le_mul_of_pos_right _ h6)).trans (Nat.le_mul_of_pos_right _ h2'))
  ·
    obtain ⟨hab, h2⟩ :=
      PartOne.Section8.exists_sylow_abelian_of_lieModel_twistedF4 hX hr (by omega) hrd
    have hf : 1 ≤ f := hX.admissible.2.1
    have hq1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    have hq2 : 2 ≤ 2 ^ f := hq1
    have hc := CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover.card_of_lieModel hX
    simp only [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator,
      CFSG.ComponentClassification.CatLeaf.lieOrderDivisor, mul_one] at hc
    refine key hr hr5 (center_bar2_eq_bot_of_is2F4 hL hX) h2 hab
      (PartOne.Section8.not_dvd_card_outer_lieModel_twistedF4 hX Nat.prime_two hr (by omega)
        hrd hrf) ?_
    rw [hc]
    have h12 : 3600 < (2 ^ f) ^ 12 :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_left hq2 12)
    have h4 : 0 < (2 ^ f) ^ 4 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) hq1)
    exact lt_of_lt_of_le h12 ((((Nat.le_mul_of_pos_right _ (by positivity)).trans
      (Nat.le_mul_of_pos_right _ h4)).trans (Nat.le_mul_of_pos_right _ (by positivity))).trans
      (Nat.le_mul_of_pos_right _ (by omega)))

end Torus

end CFSG.LocalAnalysis.UniquenessCase.UC22

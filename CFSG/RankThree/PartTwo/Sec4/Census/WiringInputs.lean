module

public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
public import CFSG.RankThree.PartTwo.Sec4.Census.Bridges
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.RankThree.PartTwo.Census.Spin.Consumers
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.RankThree.PartTwo.Census.Exceptional.ReeIndex
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.LieType.Multipliers.U43
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Suz
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
public import CFSG.Sporadic.Bridge.SuzSurj
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 TauCeti
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex
  localRank)
open CFSG.ComponentClassification.TBLit (GriessMultipliersCentralCovers)

theorem spinLargePrimeRankThree : SpinLargePrimeRankThree where
  typeB3 := CFSG.RankThree.PartTwo.Census.Spin.spinLarge_typeB3
  twistedD4 := CFSG.RankThree.PartTwo.Census.Spin.spinLarge_twistedD4

theorem griessMultipliersCentralCovers : GriessMultipliersCentralCovers :=
  @CFSG.Milestones.cl_lit_griess_schur_multipliers_central_covers

theorem localRank_reeG2_one (hr : (LieTypeIndex.reeG2 1).Valid)
    [hfin : Finite (CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group] :
    3 ≤ localRank 3 (CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group :=
  @CFSG.RankThree.PartTwo.Census.Exceptional.le_localRank_reeG2 (ReeG2LieIndex.of 1 hr) 1
    (LieTypeIndex.fieldExponent_reeG2 1) le_rfl hfin

section Chevalley

theorem bridgeExceptional46 : BridgeExceptional46 where
  g2Even q hv hq := by
    have h3 : 3 ≤ q.p ^ q.exponent := by
      have h := ((LieTypeIndex.valid_iff _).1 hv).1
      simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using h
    have h : ChevalleyExceptionalModel (CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩,
        CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
          CFSG.TauCetiBridge.Even.chevalleyBridgesEven.g2 q hv hq (MulEquiv.refl _)⟩
    rwa [hq] at h
  trialityD4 q hv hq := by
    have h : ChevalleyExceptionalModel (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group .trialityD4
        q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
          CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide)
          (MulEquiv.refl _)⟩
    rwa [hq] at h
  reeF4 m hm := by
    have hfin : ∀ d : ReeF4LieIndex, Finite d.1.fixedField := fun _ => inferInstance
    have hchar : ∀ d : ReeF4LieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
    have := hfin (ReeF4LieIndex.of m hm)
    have := hchar (ReeF4LieIndex.of m hm)
    have hm1 : 1 ≤ m :=
      (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hm).1
    have hhalf : (ReeF4LieIndex.of m hm).toSuzukiReeIndex.halfExponent = m :=
      SuzukiReeIndex.halfExponent_reeF4 m hm
    obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_reeF4 (ReeF4LieIndex.of m hm)
    rw [hhalf] at e₁
    have hK := CFSG.TauCetiBridge.ReeF4.card_fixedField_reeF4 (ReeF4LieIndex.of m hm)
    rw [hhalf] at hK
    exact ⟨⟨Nat.prime_two, by omega, ⟨rfl, rfl, ⟨m, rfl⟩, by omega⟩⟩, m, rfl,
      ⟨(ReeF4LieIndex.of m hm).1.fixedField, inferInstance, inferInstance, hK,
        ⟨e₁.trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv m).symm⟩⟩⟩
  tits ht := by
    have hfin : ∀ d : TitsLieIndex, Finite d.1.fixedField := fun _ => inferInstance
    have hchar : ∀ d : TitsLieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
    have := hfin TitsLieIndex.of
    have := hchar TitsLieIndex.of
    obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_tits TitsLieIndex.of
    exact ⟨⟨Nat.prime_two, le_rfl, ⟨rfl, rfl, rfl⟩⟩, 0, rfl,
      ⟨TitsLieIndex.of.1.fixedField, inferInstance, inferInstance,
        (CFSG.TauCetiBridge.ReeF4.card_fixedField_tits _).trans (pow_one 2).symm,
        ⟨e₁.trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv 0).symm⟩⟩⟩

theorem three_lt_pRank_f4Two : 3 < CFSG.pRank 3 (CFSGIndex.lie f4TwoIndex).Group := by
  have hm : UntwistedChevalleyModel (CFSGIndex.lie f4TwoIndex).Group .F4 (2 ^ 1) :=
    CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 CFSG.Assembly.RankThreeEven.primePowerTwo
      f4TwoIndex.2 rfl (MulEquiv.refl _)
  have : Finite (CFSGIndex.lie f4TwoIndex).Group := by
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := hm
    exact Finite.of_equiv _ e.symm.toEquiv
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  have := CFSG.SectionRank.four_le_pRank_three_of_untwistedModel_two (τ := .F4) (Or.inl rfl) hm
  omega

end Chevalley

section U43

theorem coverU43Center : CoverU43Center := by
  intro X _ _ hq hZ3 ⟨e⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm : StatedLieAdmissible .PSU 4 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  have hcl : StatedClassicalModel (projSU 4 3 1) .PSU 4 3 1 := by
    rcases lieModel_projSU (n := 4) (p := 3) (e := 1) hadm with ⟨-, h | ⟨h0, -⟩⟩
    · exact h
    · exact absurd h0 (by norm_num)
  have hm : Blueprint.LieModel (projSU 4 3 1) .PSU 4 3 1 := Or.inl ⟨by decide, hcl⟩
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.U43.multiplier_PSU_four_three _ hm
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e
  have h36 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (projSU 4 3 1)) = 36 := by
    rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
      Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_prod,
      Nat.card_prod, Nat.card_zmod, Nat.card_zmod]
  rw [h36] at hdvd
  obtain ⟨k, hk⟩ := hZ3.exists_card_eq
  rw [hk] at hdvd ⊢
  have hcop : Nat.Coprime (3 ^ k) 4 := Nat.Coprime.pow_left k (by norm_num)
  exact hcop.dvd_of_dvd_mul_right (show 3 ^ k ∣ 9 * 4 from hdvd)

theorem CoverInputs46.of_open (hsl : CoverSLThree46) (hcen : CoverCenterThree)
    (hu43r : NineCoverU43RankFour) : CoverInputs46 :=
  ⟨hsl, hcen, coverU43Center, hu43r⟩

end U43

section Suz

theorem three_lt_pRank_suz : 3 < CFSG.pRank 3 (Spor .Suz) := by
  obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.Suz_elementary_three_rank_four
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have hEA : IsElementaryAbelian 3 E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hE.2 x x.2) }
  have h4 := CFSG.LieType.SteinbergBR.le_pRank_of_card (by norm_num) E hEA hc
  have : Finite SporadicName.Suz.Group := Finite.of_equiv _ b.toEquiv
  have heq : CFSG.pRank 3 Blueprint.NativeSporadic.Suz = CFSG.pRank 3 (Spor .Suz) :=
    CFSG.RankThree.PartTwo.pRank_congr_mulEquiv (by norm_num) b
  omega

end Suz

structure RankThree46Open : Prop where
  sporadic : ∀ s ∈ sporadics42not46, ∀ [Finite (CFSGIndex.sporadic s).Group],
    3 ≤ localRank 3 (CFSGIndex.sporadic s).Group
  omega8PlusTwo : ∀ [Finite (projOmegaPlus 4 (GaloisField 2 1))],
    3 ≤ localRank 3 (projOmegaPlus 4 (GaloisField 2 1))
  omega8MinusTwo : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
    ∀ [Finite (projOmegaMinus 3 (GaloisField 2 1) b c)],
      3 ≤ localRank 3 (projOmegaMinus 3 (GaloisField 2 1) b c)
  f4Two : ∀ [Finite (CFSGIndex.lie f4TwoIndex).Group],
    3 ≤ localRank 3 (CFSGIndex.lie f4TwoIndex).Group

theorem RankThree46.of_open (h : RankThree46Open) : RankThree46 :=
  ⟨localRank_reeG2_one, h.sporadic, h.omega8PlusTwo, h.omega8MinusTwo, h.f4Two⟩

structure TwoCoverRanksOpen : Prop where
  alternating : ∀ n : ℕ, 6 ≤ n → n ≤ 12 → NoRankThreeDoubleCover (alternatingGroup (Fin n))
  hs : NoRankThreeDoubleCover (Spor .HS)
  ru : NoRankThreeDoubleCover (Spor .Ru)
  m22 : NoRankThreeDoubleCover (Spor .M22)
  psu42 : NoRankThreeDoubleCover (projSU 4 2 1)
  psl34 : ∀ (J : Type) [Group J] [Finite J], IsTwoCover J (projSL 3 (GaloisField 2 2)) →
    CFSG.pRank 2 J = 3 → IsCyclic (Subgroup.center J) ∧ Nat.card (Subgroup.center J) = 4
  g24 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
    q.exponent = 2 → NoRankThreeDoubleCover (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  sz8 : ∀ hm : (TauCeti.LieTypeIndex.suzuki 1).Valid,
    NoRankThreeTwoCover (TauCeti.CFSGIndex.lie ⟨.suzuki 1, hm⟩).Group
  sp62 : NoRankThreeDoubleCover (projSp 3 (GaloisField 2 1))
  omegaPlus : 3 < CFSG.pRank 3 (projOmegaPlus 4 (GaloisField 2 1))

section Bundles

theorem Inputs46.of_open (hsl : CoverSLThree46) (hcen : CoverCenterThree)
    (hu43r : NineCoverU43RankFour) (hrank : RankThree46Open) : Inputs46 :=
  ⟨CoverInputs46.of_open hsl hcen hu43r, bridgeExceptional46, RankThree46.of_open hrank⟩

end Bundles

section Ranks

theorem TwoCoverRanks.of_open (h : TwoCoverRanksOpen) : TwoCoverRanks where
  alternating := h.alternating
  hs := h.hs
  ru := h.ru
  m22 := h.m22
  suz := three_lt_pRank_suz
  psu42 := h.psu42
  psl34 := h.psl34
  g24 := h.g24
  sz8 := h.sz8
  sp62 := h.sp62
  omegaPlus := h.omegaPlus
  f42 := three_lt_pRank_f4Two

end Ranks

end CFSG.RankThree.PartTwo.Sec4.Census

module

public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeNarrow
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec4
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofOuter
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofExc
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzOther
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.OuterThreeAll
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofKit

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2

@[expose] def SeitzThreePartTwoChar2 : Prop :=
  SeitzPlanes fun d p _ =>
    p = 3 ∧ (IsLThreePiIndex d.1 ∨ IsTrialityIndex d.1 ∨ IsSeitz441Index d.1) ∧
      d.1.characteristic = 2

end CFSG.RankThree.PartTwo.Sec19

namespace CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo TauCeti CFSG.AGLEmbeddingD2
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res6Seitz
open CFSG.LieType.SeitzGeneration
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)


theorem seitzHyperGamma_eq_top_of_carrier_char2 (hS : SeitzThreePartTwoChar2) {X : Type} [Group X]
    {d : ValidLieTypeIndex} (hd : IsLThreePiIndex d.1 ∨ IsTrialityIndex d.1 ∨ IsSeitz441Index d.1)
    (hc2 : d.1.characteristic = 2) (hexc : ¬ IsD2SeitzException 3 d.1)
    (ι : X ≃* (CFSGIndex.lie d).Group) {E : Subgroup (MulAut X)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h9 : Nat.card E = 9) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤ := by
  have hchar : 3 ≠ d.1.characteristic := by rw [hc2]; norm_num
  exact Item434RowsProof.seitzHyperGamma_eq_top_of_closure hE.2 h9
    (closure_fixSet_eq_top_of_seitzPlanes hS hchar hexc ι E ⟨hE.1, hE.2⟩ h9 ⟨rfl, hd, hc2⟩)

end CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof

section Certs


namespace CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo TauCeti CFSG.AGLEmbeddingD2
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res6Seitz
open CFSG.LieType.SeitzGeneration
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)


theorem seitzHyperGamma_eq_top_of_projSL_char2 (hS : SeitzThreePartTwoChar2) {X : Type} [Group X]
    {r p e : ℕ} [Fact p.Prime] (hr : 2 ≤ r) (he : 1 ≤ e) (hp2 : p = 2) (hq : 3 ≤ p ^ e)
    (h4 : ¬ (r = 2 ∧ p ^ e = 4)) (φ : X ≃* projSL (r + 1) (GaloisField p e))
    {E : Subgroup (MulAut X)} (hE : CFSG.Assembly.IsElemAbelian 3 E) (h9 : Nat.card E = 9)
    (hr3 : r ≤ 3 := by norm_num) : CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤ := by
  have hp : p.Prime := Fact.out
  set q : PrimePower := ⟨p, e, hp, by omega⟩ with hqdef
  have hqc : q.card = p ^ e := PrimePower.card_def q
  have hv : (LieTypeIndex.A r q).Valid := by
    refine ⟨⟨by omega, fun h => by omega⟩, ?_⟩
    change ¬ ((r = 1 ∧ (q.card = 4 ∨ q.card = 5 ∨ q.card = 9)) ∨ (r = 2 ∧ q.card = 2) ∨
      (r = 3 ∧ q.card = 2))
    rw [hqc]
    omega
  refine seitzHyperGamma_eq_top_of_carrier_char2 hS (d := ⟨.A r q, hv⟩) (scope_A q hr hr3) ?_ ?_
    (φ.trans ((Sec4.projSLEquivPSLn (r + 1) _).trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).symm)) hE h9
  · change (LieTypeIndex.A r q).characteristic = 2
    rw [LieTypeIndex.characteristic_A]
    exact hp2
  · simp only [IsD2SeitzException]
    rintro (⟨-, (⟨q', hq'2, hq'3, hd⟩ | ⟨q', hq'2, hq'3, hd⟩ | ⟨q', -, -, hd⟩ |
      ⟨q', -, -, hd | hd⟩ | hd)⟩ | ⟨h5, -⟩)
    · exact absurd (LieTypeIndex.A.inj hd).1 (by omega)
    · obtain ⟨hr2, hqq⟩ := LieTypeIndex.A.inj hd
      apply h4
      refine ⟨hr2, ?_⟩
      rw [← hqc, hqq, PrimePower.card_def, hq'2, hq'3]
      norm_num
    · cases hd
    · cases hd
    · cases hd
    · cases hd
    · omega

theorem seitzHyperGamma_eq_top_of_projSU_char2 (hS : SeitzThreePartTwoChar2) {X : Type} [Group X]
    {r p e : ℕ} [Fact p.Prime] (hr : 2 ≤ r) (he : 1 ≤ e) (hp2 : p = 2) (hq : 3 ≤ p ^ e)
    (φ : X ≃* projSU (r + 1) p e)
    {E : Subgroup (MulAut X)} (hE : CFSG.Assembly.IsElemAbelian 3 E) (h9 : Nat.card E = 9)
    (hr3 : r ≤ 3 := by norm_num) : CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤ := by
  have hp : p.Prime := Fact.out
  set q : PrimePower := ⟨p, e, hp, by omega⟩ with hqdef
  have hqc : q.card = p ^ e := PrimePower.card_def q
  have hv : (LieTypeIndex.twistedA r q).Valid :=
    ⟨⟨hr, fun _ => by rw [hqc]; exact hq⟩, fun h => h⟩
  refine seitzHyperGamma_eq_top_of_carrier_char2 hS (d := ⟨.twistedA r q, hv⟩)
    (scope_twistedA q hr hr3) ?_ ?_
    (φ.trans ((Sec4.projSUEquivStatedProj (r + 1) p e).trans
      (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv).symm)) hE h9
  · change (LieTypeIndex.twistedA r q).characteristic = 2
    rw [LieTypeIndex.characteristic_twistedA]
    exact hp2
  · simp only [IsD2SeitzException]
    rintro (⟨-, (⟨q', -, -, hd⟩ | ⟨q', -, -, hd⟩ | ⟨q', hq'2, hq'3, hd⟩ |
      ⟨q', -, -, hd | hd⟩ | hd)⟩ | ⟨h5, -⟩)
    · cases hd
    · cases hd
    · obtain ⟨-, hqq⟩ := LieTypeIndex.twistedA.inj hd
      have : q.card = 2 := by rw [hqq, PrimePower.card_def, hq'2, hq'3]; rfl
      omega
    · cases hd
    · cases hd
    · cases hd
    · omega

theorem seitzHyperGamma_eq_top_of_projSp_char2 (hS : SeitzThreePartTwoChar2) {X : Type} [Group X]
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (hp2 : p = 2) (hq : 4 ≤ p ^ e)
    (φ : X ≃* projSp 2 (GaloisField p e))
    {E : Subgroup (MulAut X)} (hE : CFSG.Assembly.IsElemAbelian 3 E) (h9 : Nat.card E = 9) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤ := by
  have hp : p.Prime := Fact.out
  set q : PrimePower := ⟨p, e, hp, by omega⟩ with hqdef
  have hqc : q.card = p ^ e := PrimePower.card_def q
  have hv : (LieTypeIndex.B 2 q).Valid := by
    refine ⟨⟨le_rfl, ?_⟩, ?_⟩
    · rw [hqc]
      omega
    · change ¬ (2 = 2 ∧ q.card = 3)
      rw [hqc]
      omega
  have : Fact q.p.Prime := ⟨hp⟩
  refine seitzHyperGamma_eq_top_of_carrier_char2 hS (d := ⟨.B 2 q, hv⟩) (scope_B2 q) ?_ ?_
    (φ.trans (Census.typeB2GroupEquivProjSp q hv).symm) hE h9
  · change (LieTypeIndex.B 2 q).characteristic = 2
    rw [LieTypeIndex.characteristic_B]
    exact hp2
  · simp only [IsD2SeitzException]
    rintro (⟨-, (⟨q', -, -, hd⟩ | ⟨q', -, -, hd⟩ | ⟨q', -, -, hd⟩ |
      ⟨q', -, -, hd | hd⟩ | hd)⟩ | ⟨h5, -⟩)
    · cases hd
    · cases hd
    · cases hd
    · cases hd
    · cases hd
    · cases hd
    · omega

theorem seitzHyperGamma_eq_top_other_nine_char2 (hS : SeitzThreePartTwoChar2) {X : Type}
    [Group X] [Finite X] (hq : IsQuasisimple X) (hZ3 : IsPGroup 3 (Subgroup.center X))
    (hL : IsSmallTwoOtherField (X ⧸ Subgroup.center X)) {E : Subgroup (MulAut X)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h9 : Nat.card E = 9) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hL with hθ | hθ | hθ | hθ | ⟨q, hq2, hq6, hv, ⟨θ⟩⟩ |
    ⟨q, hv, hq2, -, ⟨θ⟩⟩ | ⟨m, hm, -, ⟨θ⟩⟩
  ·
    obtain ⟨θ⟩ := hθ
    have hK : Nat.card (GaloisField 2 3) = 8 := by
      rw [GaloisField.card 2 3 (by norm_num)]; norm_num
    have hZ := center_eq_bot_of_projSL_three hq hZ3 (by rw [hK]) θ
    exact seitzHyperGamma_eq_top_of_projSL_char2 hS (r := 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (equivOfCenterEqBot hZ θ) hE h9
  ·
    obtain ⟨θ⟩ := hθ
    have hZ := center_eq_bot_of_projSU_three hq hZ3 (by norm_num) (by norm_num) θ
    exact seitzHyperGamma_eq_top_of_projSU_char2 hS (r := 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (equivOfCenterEqBot hZ θ) hE h9
  ·
    obtain ⟨θ⟩ := hθ
    have hK : Nat.card (GaloisField 2 6) = 64 := by
      rw [GaloisField.card 2 6 (by norm_num)]; norm_num
    have hZ := center_eq_bot_of_projSp_two hq hZ3 (by rw [hK]; norm_num) θ
    exact seitzHyperGamma_eq_top_of_projSp_char2 hS (by norm_num) (by norm_num) (by norm_num)
      (equivOfCenterEqBot hZ θ) hE h9
  ·
    obtain ⟨θ⟩ := hθ
    have hZ := center_eq_bot_of_projSU_four hq hZ3 (by norm_num) (by norm_num) θ
    exact seitzHyperGamma_eq_top_of_projSU_char2 hS (r := 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (equivOfCenterEqBot hZ θ) hE h9
  ·
    have hmod : CFSG.Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 2
        q.exponent :=
      CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv θ
        (Census.bridgeExceptional46.g2Even q hv hq2)
    have hZ := center_eq_bot_of_G2 hq hmod (by rw [hq6]; norm_num)
    refine seitzHyperGamma_eq_top_of_carrier_char2 hS (d := ⟨.G2 q, hv⟩) (scope_G2 q) ?_
      (not_isD2SeitzException_G2 q) (equivOfCenterEqBot hZ θ) hE h9
    change (LieTypeIndex.G2 q).characteristic = 2
    rw [LieTypeIndex.characteristic_G2, hq2]
  ·
    have hmod : CFSG.Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .trialityD4 2
        q.exponent :=
      CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv θ
        (Census.bridgeExceptional46.trialityD4 q hv hq2)
    have hZ := center_eq_bot_of_trialityD4 hq hZ3 hmod
    refine seitzHyperGamma_eq_top_of_carrier_char2 hS (d := ⟨.trialityD4 q, hv⟩)
      (scope_trialityD4 q) ?_ (not_isD2SeitzException_trialityD4 q)
      (equivOfCenterEqBot hZ θ) hE h9
    change (LieTypeIndex.trialityD4 q).characteristic = 2
    rw [LieTypeIndex.characteristic_trialityD4, hq2]
  ·
    have hZ := center_eq_bot_of_reeF4 hq hZ3 hm θ
    refine seitzHyperGamma_eq_top_of_carrier_char2 hS (d := ⟨.reeF4 m, hm⟩) (scope_reeF4 m) ?_
      (not_isD2SeitzException_reeF4 m) (equivOfCenterEqBot hZ θ) hE h9
    change (LieTypeIndex.reeF4 m).characteristic = 2
    rw [LieTypeIndex.characteristic_reeF4]

theorem seitzThreeSec441Char2_of_noninner (hN : SeitzThreeSec441NoninnerTwo)
    (hR : SeitzExcAnisotropicReeF4Three) :
    SeitzPlanes fun d p _ => p = 3 ∧ IsSeitz441Index d.1 ∧ d.1.characteristic = 2 := by
  intro d p hp hp2 hpd hex E hE hc ⟨hp3, hd, hc2⟩
  by_cases hin : InnerPlane d p E
  · rcases hd with hk | hG | hRe
    · exact seitzThreeSec441Inner d p hp hp2 hpd hex E hE hc ⟨hin, hp3, hk⟩
    · exact seitzThreeG2Inner d p hp hp2 hpd hex E hE hc ⟨hin, hp3, hG⟩
    · exact seitzThreeReeF4Inner_of hR d p hp hp2 hpd hex E hE hc ⟨hin, hp3, hRe⟩
  · exact hN d p hp hp2 hpd hex E hE hc ⟨hin, hp3, hd, hc2⟩

theorem seitzThreeLThreePiChar2_of (hF : SeitzThreeLThreePiFieldTwo) :
    SeitzPlanes fun d p _ => p = 3 ∧ IsLThreePiIndex d.1 ∧ d.1.characteristic = 2 := by
  intro d p hp hp2 hpd hex E hE hc ⟨hp3, hd, hc2⟩
  by_cases hin : InnerPlane d p E
  · exact seitzThreeLThreePiInner d p hp hp2 hpd hex E hE hc ⟨hin, hp3, hd⟩
  · by_cases hs : NarrowScope p E
    · exact seitzThreeLThreePiOuterNarrow d p hp hp2 hpd hex E hE hc ⟨hin, hs, hp3, hd⟩
    · exact hF d p hp hp2 hpd hex E hE hc ⟨hin, hs, hp3, hd, hc2⟩

theorem seitzThreeTrialityChar2_of (hT : SeitzThreeTrialityWideTwo)
    (hA : SeitzExcAnisotropicTrialityThreeTwo) (hO : SeitzExcOuterNarrowTrialityThree) :
    SeitzPlanes fun d p _ => p = 3 ∧ IsTrialityIndex d.1 ∧ d.1.characteristic = 2 := by
  intro d p hp hp2 hpd hex E hE hc ⟨hp3, hd, hc2⟩
  by_cases hin : InnerPlane d p E
  · by_cases hN : NormalizesRSubgroup d E
    · exact seitzExcParabolic d p hp hp2 hpd hex E hE hc
        ⟨hin, IsTrialityIndex.not_classical hd, hN⟩
    · by_cases hr : RankLE2 p (Cat d)
      · exact hA d p hp hp2 hpd hex E hE hc ⟨hin, hd, ⟨hp3, hc2⟩, hr, hN⟩
      · exact hT d p hp hp2 hpd hex E hE hc ⟨hp3, hd, hc2, Or.inr ⟨hin, hr⟩⟩
  · by_cases hs : NarrowScope p E
    · exact hO d p hp hp2 hpd hex E hE hc ⟨hin, hs, hd, hp3⟩
    · exact hT d p hp hp2 hpd hex E hE hc ⟨hp3, hd, hc2, Or.inl ⟨hin, hs⟩⟩

theorem seitzThreePartTwoChar2_of (hF : SeitzThreeLThreePiFieldTwo)
    (hN : SeitzThreeSec441NoninnerTwo) (hT : SeitzThreeTrialityWideTwo)
    (hA : SeitzExcAnisotropicTrialityThreeTwo) (hR : SeitzExcAnisotropicReeF4Three) :
    SeitzThreePartTwoChar2 := by
  intro d p hp hp2 hpd hex E hE hc ⟨hp3, h, hc2⟩
  rcases h with h | h | h
  · exact seitzThreeLThreePiChar2_of hF d p hp hp2 hpd hex E hE hc ⟨hp3, h, hc2⟩
  · exact seitzThreeTrialityChar2_of hT hA
      CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.seitzExcOuterNarrowTrialityThree_proved
      d p hp hp2 hpd hex E hE hc ⟨hp3, h, hc2⟩
  · exact seitzThreeSec441Char2_of_noninner hN hR d p hp hp2 hpd hex E hE hc ⟨hp3, h, hc2⟩

end CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof
open CFSG.LieType.SeitzGeneration

theorem seitz434Other_of_seitzThreeChar2 (hS : SeitzThreePartTwoChar2)
    (h27 : Seitz434OtherTwentySeven) : Seitz434Other := by
  intro X _ _ hq hZ3 hL E hE hc
  rcases hc with h9 | ⟨h27', hZ⟩
  · exact seitzHyperGamma_eq_top_other_nine_char2 hS hq hZ3 hL hE h9
  · exact h27 X hq hZ hL E hE h27'

theorem seitz434Other_of_seitzFieldTwo (hF : SeitzThreeLThreePiFieldTwo)
    (hN : SeitzThreeSec441NoninnerTwo) (hT : SeitzThreeTrialityWideTwo)
    (hA : SeitzExcAnisotropicTrialityThreeTwo) (hR : SeitzExcAnisotropicReeF4Three)
    (h27 : Seitz434OtherTwentySeven) : Seitz434Other :=
  seitz434Other_of_seitzThreeChar2 (seitzThreePartTwoChar2_of hF hN hT hA hR) h27

end CFSG.RankThree.PartTwo.Sec4

end Certs

end

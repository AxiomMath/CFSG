module

public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOExcB
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOExcOdd
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOExcSmall
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LH1Rows
import CFSG.HardMathSupport.Lang.AnisoE6.F4InTwistedE6

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup lieIndexChar)
open TauCeti (PrimePower LieTypeIndex)

set_option linter.unusedSectionVars false


theorem not_threeRankLeOneInv_cat_untw {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (q : PrimePower) (hv : (c q).Valid)
    (hτ : τ ≠ .G2 ∨ q.p ≠ 2) {L : Type} [Group L]
    (e : L ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group) : ¬ ThreeRankLeOneInv L := by
  obtain ⟨K, _, _, -, hch, ⟨e'⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  haveI := hch
  exact not_threeRankLeOneInv_of_mulEquiv_adjoint
    (hτ.imp id fun h => by rw [ringChar.eq K q.p]; exact h) (e.trans e')

theorem not_threeRankLeOneInv_cat_D4 (q : PrimePower) (hv : (LieTypeIndex.D 4 q).Valid)
    {L : Type} [Group L] (e : L ≃* (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) :
    ¬ ThreeRankLeOneInv L := by
  obtain ⟨K, _, _, -, -, ⟨e'⟩⟩ := CFSG.LieType.SeitzGeneration.ExcWideThree.exists_catEquiv_D4 q hv
  exact not_threeRankLeOneInv_of_mulEquiv_adjoint (Or.inl (by decide)) (e.trans e')

theorem not_threeRankLeOneInv_cat_twistedE6 (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid) {L : Type} [Group L]
    (e : L ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) : ¬ ThreeRankLeOneInv L := by
  obtain ⟨K, _, σ, hK, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Finite (fixSubfield σ) := Subtype.finite
  have hfix : ∀ c : fixSubfield σ, σ (algebraMap (fixSubfield σ) K c) =
      algebraMap (fixSubfield σ) K c := fun c => c.2
  exact not_threeRankLeOneInv_of_adjoint (τ := .F4) (K := fixSubfield σ) (Or.inl (by decide))
    (ι := (e.trans eK).symm.toMonoidHom.comp
      ((CFSG.HardMathSupport.Lang.AnisoE6.phiG σ hfix).comp
        (CFSG.HardMathSupport.Lang.AnisoE6.e6FixedF4EquivAll (fixSubfield σ)).symm.toMonoidHom))
    ((e.trans eK).symm.injective.comp
      (CFSG.HardMathSupport.Lang.AnisoE6.f4InTwistedE6_injective σ hfix))

theorem not_threeRankLeOneInv_cat_trialityD4 (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid) (hq2 : q.p ≠ 2) (hq3 : q.p ≠ 3) {L : Type}
    [Group L] (e : L ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) :
    ¬ ThreeRankLeOneInv L := by
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have h5 : 5 ≤ q.p := by
    have h2 := q.prime_p.two_le
    have h4 : q.p ≠ 4 := fun h => by
      have := q.prime_p
      rw [h] at this
      exact absurd this (by norm_num)
    omega
  obtain ⟨eG⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_fixSubgroup_fieldActor_equiv_G2
    (ℓ := q.p) (f := q.exponent) hq3 q.exponent_pos (Or.inr h5) hK σ hσ
  haveI : CharP K q.p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.charP_of_card_pow_three q.prime_p
      q.exponent_pos hK
  have hch : ringChar (fixSubfield σ) ≠ 2 := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_subfield (ringChar.eq K q.p)]
    exact hq2
  exact not_threeRankLeOneInv_of_adjoint (τ := .G2) (Or.inr hch)
    (ι := (e.trans eK).symm.toMonoidHom.comp
      ((fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)).subtype.comp eG.symm.toMonoidHom))
    ((e.trans eK).symm.injective.comp (Subtype.val_injective.comp eG.symm.injective))

theorem ff79KLemmaOExc_holds : FF79KLemmaOExc := by
  intro L _ _ hs hna d hexc he _ hB x hx3 hout K hKO hquot
  by_cases hc : lieIndexChar d.1 = 2 ∨ lieIndexChar d.1 = 5
  swap
  · push Not at hc
    have hfix : fixSubgroup x = CFSG.RankThree.PartTwo.Sec4.autFix x :=
      Subgroup.ext fun _ => Iff.rfl
    obtain ⟨hKle, hsn, hq⟩ := hKO
    rw [hfix] at hKle hsn
    exact CFSG.RankThree.PartTwo.Sec4.Ronan148L.noA5ONAt_of_lie hs hna d hc.1 hc.2 he x hx3 K hKle
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).2 hq))
      ((CFSG.Open.IsSubnormal.iff_subgroupOf hKle).1 hsn) (Or.inl hquot)
  have hc3 : lieIndexChar d.1 ≠ 3 := by omega
  obtain ⟨e⟩ := he
  have hout' : ∀ c : L, MulAut.conj c ≠ x := fun c h => hout c h.symm
  obtain ⟨d, hv⟩ := d
  cases d with
  | B r q =>
    exact noA5_omegaOdd_outer Nat.prime_three (by norm_num)
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hexc.2 hexc.1 e)
      x hx3 hout' K hKO hquot
  | D r q =>
    obtain rfl : r = 4 := by
      rcases r with _ | _ | _ | _ | _ | r <;> first | rfl | exact hexc.elim
    exact not_threeRankLeOneInv_cat_D4 q hv e hB
  | E6 q =>
    exact not_threeRankLeOneInv_cat_untw CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
      (Or.inl (by decide)) e hB
  | E7 q =>
    exact not_threeRankLeOneInv_cat_untw CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
      (Or.inl (by decide)) e hB
  | E8 q =>
    exact not_threeRankLeOneInv_cat_untw CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
      (Or.inl (by decide)) e hB
  | F4 q =>
    exact not_threeRankLeOneInv_cat_untw CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
      (Or.inl (by decide)) e hB
  | G2 q =>
    by_cases hq2 : q.p = 2
    · have hq8 : q.card < 8 := by
        have h : q.p ≠ 2 ∨ q.card < 8 := hexc
        omega
      obtain ⟨c, hc⟩ := exists_conj_of_g2_small hv hq2 hq8 e hx3
      exact hout c hc
    · exact not_threeRankLeOneInv_cat_untw CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
        (Or.inr hq2) e hB
  | twistedE6 q => exact not_threeRankLeOneInv_cat_twistedE6 q hv e hB
  | trialityD4 q =>
    by_cases hq2 : q.p = 2
    · exact noA5_triD4_two_outer q hv hq2 ⟨e⟩ x hx3 hout' K hKO hquot
    · exact not_threeRankLeOneInv_cat_trialityD4 q hv hq2 hc3 e hB
  | reeF4 m => exact noA5_reeF4_outer m hv e x hx3 hout K hKO hquot
  | tits =>
    obtain ⟨c, hc⟩ := exists_conj_of_tits hv ⟨e⟩ hx3
    exact hout c hc
  | A _ _ => exact hexc.elim
  | twistedA _ _ => exact hexc.elim
  | C _ _ => exact hexc.elim
  | twistedD _ _ => exact hexc.elim
  | suzuki _ => exact hexc.elim
  | reeG2 _ => exact hexc.elim

end CFSG.RankThree.PartTwo.Sec21.FF79

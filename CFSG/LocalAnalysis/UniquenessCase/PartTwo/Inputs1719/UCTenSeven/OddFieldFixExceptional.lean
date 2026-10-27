module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddFieldFixBase
import CFSG.LocalAnalysis.StandardType.GGExcFieldRankTransfer
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldDiag
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

private lemma card_adjointGroup_untwisted
    {K : Type} [Field K] [Finite K] {τ : CFSG.Blueprint.Chevalley.Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    Nat.card (CFSG.Blueprint.Chevalley.adjointGroup τ K) =
      (match τ with
       | .G2 => CFSG.EvenSmallLie.CatalogOrders.lieOrd .G2 0 (Nat.card K)
       | .F4 => CFSG.EvenSmallLie.CatalogOrders.lieOrd .F4 0 (Nat.card K)
       | .E6 => CFSG.EvenSmallLie.CatalogOrders.lieOrd .E6 0 (Nat.card K)
       | .E7 => CFSG.EvenSmallLie.CatalogOrders.lieOrd .E7 0 (Nat.card K)
       | .E8 => CFSG.EvenSmallLie.CatalogOrders.lieOrd .E8 0 (Nat.card K)
       | _ => 0) := by
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2
  · exact CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4
  · exact CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6
  · exact CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7
  · exact CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8

private lemma fixesSylowOutside_untwisted_of_entrywise
    {X : Type} [Group X] [Finite X] {τ : CFSG.Blueprint.Chevalley.Tag}
    {t : CFSG.Open.StatedLieTag}
    {K : Type} [Field K] [Finite K] {p r f : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (hK : Nat.card K = r ^ f)
    (hcard_all : ∀ (L : Type) [Field L] [Finite L],
      Nat.card (CFSG.Blueprint.Chevalley.adjointGroup τ L) =
        CFSG.EvenSmallLie.CatalogOrders.lieOrd t 0 (Nat.card L))
    (e : X ≃* CFSG.Blueprint.Chevalley.adjointGroup τ K)
    (σ : K ≃+* K) (hσ : orderOf σ = p)
    (δ : MulAut (CFSG.Blueprint.Chevalley.adjointGroup τ K)) (α : MulAut X)
    (hδ : δ * MulAut.congr e α * δ⁻¹ = CFSG.LieType.Chevalley.entrywiseAdjointAut τ σ) :
    ∃ S₀ : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 S₀ ⊤ ∧ ∀ x ∈ S₀, α x = x := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hrf, hcard_fix⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hr hf hK σ
  rw [hσ] at hrf hcard_fix
  let k := CFSG.LieType.Chevalley.fixSubfield σ
  have hkcard : Nat.card k = r ^ (f / p) := hcard_fix
  let ι : CFSG.Blueprint.Chevalley.adjointGroup τ k →*
      CFSG.Blueprint.Chevalley.adjointGroup τ K :=
    δ.symm.toMonoidHom.comp (CFSG.LieType.Chevalley.fixedFieldInclusion (τ := τ) σ)
  have hι : Function.Injective ι :=
    δ.symm.injective.comp (CFSG.LieType.Chevalley.fixedFieldInclusion_injective σ)
  let ι' : CFSG.Blueprint.Chevalley.adjointGroup τ k →* X := e.symm.toMonoidHom.comp ι
  have hι' : Function.Injective ι' := e.symm.injective.comp hι
  have hfix' : ∀ y, α (ι' y) = ι' y := by
    intro y
    apply e.injective
    simp only [ι', ι, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe]
    change e (α (e.symm (δ.symm (CFSG.LieType.Chevalley.fixedFieldInclusion σ y)))) =
      e (e.symm (δ.symm (CFSG.LieType.Chevalley.fixedFieldInclusion σ y)))
    rw [e.apply_symm_apply (δ.symm (CFSG.LieType.Chevalley.fixedFieldInclusion σ y))]
    change (MulAut.congr e α) ((MulEquiv.symm δ) ((LieType.Chevalley.fixedFieldInclusion σ) y)) =
      (MulEquiv.symm δ) ((LieType.Chevalley.fixedFieldInclusion σ) y)
    have h := congrArg (fun β : MulAut (CFSG.Blueprint.Chevalley.adjointGroup τ K) =>
      β (CFSG.LieType.Chevalley.fixedFieldInclusion σ y)) hδ
    simp only [MulAut.mul_apply, MulAut.inv_apply] at h
    rw [CFSG.StandardType.entrywise_fixedFieldInclusion σ y] at h
    have h' : δ ((MulAut.congr e α) (δ.symm (CFSG.LieType.Chevalley.fixedFieldInclusion σ y))) =
        δ (δ.symm (CFSG.LieType.Chevalley.fixedFieldInclusion σ y)) := by
      rw [MulEquiv.apply_symm_apply]
      exact h
    exact δ.injective h'
  have hcard' : (Nat.card (CFSG.Blueprint.Chevalley.adjointGroup τ k)).factorization 2 =
      (Nat.card X).factorization 2 := by
    have hXcard : Nat.card X = CFSG.EvenSmallLie.CatalogOrders.lieOrd t 0 (r ^ f) := by
      rw [Nat.card_congr e.toEquiv, hcard_all K, hK]
    have hkcard' : Nat.card (CFSG.Blueprint.Chevalley.adjointGroup τ k) =
        CFSG.EvenSmallLie.CatalogOrders.lieOrd t 0 (r ^ (f / p)) := by
      rw [hcard_all k, hkcard]
    rw [hXcard, hkcard']
    have hpow : (r ^ (f / p)) ^ p = r ^ f := by
      rw [← pow_mul, Nat.div_mul_cancel hrf]
    rw [← hpow]
    have hq : Odd (r ^ (f / p)) := (hr.odd_of_ne_two hr2).pow
    have hk : Odd p := hp.odd_of_ne_two (by omega)
    exact (factorization_two_lieOrd_pow t 0 hq hk).symm
  exact exists_isSylowOf_fixed_of_injective ι' hι' α hfix' hcard'


private lemma congr_not_mem_conj_range {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {α : MulAut X} (hout : α ∉ inner X) :
    MulAut.congr e α ∉ (MulAut.conj : Y →* MulAut Y).range := by
  rintro ⟨x, hx⟩
  apply hout
  refine ⟨e.symm x, ?_⟩
  ext g
  have h := congrArg (fun β : MulAut Y => e.symm (β (e g))) hx
  simpa [MulAut.congr_apply, MulAut.conj_apply] using h

private lemma fixesSylowOutside_FE
    {X : Type} [Group X] [Finite X] {τ : CFSG.Blueprint.Chevalley.Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {t : CFSG.Open.StatedLieTag}
    {K : Type} [Field K] [Finite K] {p r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf : 1 ≤ f) (hK : Nat.card K = r ^ f)
    (hcard_all : ∀ (L : Type) [Field L] [Finite L],
      Nat.card (CFSG.Blueprint.Chevalley.adjointGroup τ L) =
        CFSG.EvenSmallLie.CatalogOrders.lieOrd t 0 (Nat.card L))
    (e : X ≃* CFSG.Blueprint.Chevalley.adjointGroup τ K) (α : MulAut X)
    (hαord : orderOf α = p) (hout : α ∉ inner X) :
    ∃ S₀ : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 S₀ ⊤ ∧ ∀ x ∈ S₀, α x = x := by
  have : Fact r.Prime := ⟨hr⟩
  have hθ' : orderOf (MulAut.congr e α) = p :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hαord
  have : CharP K r := CFSG.SectionRank.charP_of_natCard_eq_pow hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K r]; exact hr2
  obtain ⟨σ, δ, hσ, hδ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.exists_conj_entrywise_exc_of_diag
      hτ hK2 hp (by omega) (fun _ => Or.inl (by omega))
      (hθ' ▸ pow_orderOf_eq_one (MulAut.congr e α)) (congr_not_mem_conj_range e hout)
  exact fixesSylowOutside_untwisted_of_entrywise hr hr2 hp hp5 hf hK hcard_all e σ hσ δ α hδ

theorem fixesSylowOutside_untwisted
    {X : Type} [Group X] [Finite X] {t : CFSG.Open.StatedLieTag}
    {n r f : ℕ} (ht : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (hr2 : r ≠ 2)
    (hadm : CFSG.Open.StatedLieAdmissible t n r f) (hX : CFSG.Blueprint.LieModel X t n r f)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : FixesSylowOutside X (inner X) p := by
  intro α hα hout
  have hr : r.Prime := hadm.1
  have : Fact r.Prime := ⟨hr⟩
  have hαne : α ≠ 1 := by
    intro h1
    apply hout
    rw [h1]
    exact Subgroup.one_mem _
  have hαord : orderOf α = p := by
    have hdvd := orderOf_dvd_of_pow_eq_one hα
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | hp1
    · exact absurd (orderOf_eq_one_iff.mp h1) hαne
    · exact hp1
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨_, K, _, _, hK, ⟨e0⟩⟩ :=
      hX.chevalleyExceptionalModel (by simp [CFSG.Blueprint.chevalleyExceptionalTags])
    let e := e0.trans ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot_field
        CFSG.Blueprint.Chevalley.Tag.G2 K)).trans QuotientGroup.quotientBot)
    have hθ' : orderOf (MulAut.congr e α) = p :=
      (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hαord
    have hout' := congr_not_mem_conj_range e hout
    obtain ⟨x, σ, hσ, hform⟩ : ∃ (x : CFSG.Blueprint.Chevalley.adjointGroup .G2 K)
        (σ : K ≃+* K), orderOf σ = p ∧ MulAut.congr e α =
          MulAut.conj x * CFSG.LieType.Chevalley.entrywiseAdjointAut .G2 σ := by
      by_cases hr3 : r = 3
      · subst r
        have : CharP K 3 := CFSG.SectionRank.charP_of_natCard_eq_pow hK
        exact CFSG.HardMathSupport.Lang.E6Descent.G2_form_three hadm.2.1 K hK hp
          (by omega) (MulAut.congr e α) hθ' hout'
      · exact CFSG.HardMathSupport.Lang.E6Descent.G2_form_odd hr hr2 hr3 hadm.2.1 K hK hp
          (MulAut.congr e α) hθ' hout'
    obtain ⟨δ, hδ⟩ :=
      CFSG.HardMathSupport.Lang.E6Descent.exists_conj_eq_entrywiseAdjointAut_of_form
        .G2 hr hadm.2.1 K hK hp (MulAut.congr e α) hθ' x σ hσ hform
    exact fixesSylowOutside_untwisted_of_entrywise hr hr2 hp hp5 hadm.2.1 hK
      (fun L _ _ => card_adjointGroup_untwisted (Or.inl rfl) (K := L)) e σ hσ δ α hδ
  · obtain ⟨_, K, _, _, hK, ⟨e0⟩⟩ :=
      hX.chevalleyExceptionalModel (by simp [CFSG.Blueprint.chevalleyExceptionalTags])
    exact fixesSylowOutside_FE (Or.inl rfl) hr hr2 hp hp5 hadm.2.1 hK
      (fun L _ _ => card_adjointGroup_untwisted (Or.inr (Or.inl rfl)) (K := L))
      (e0.trans ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot_field
          CFSG.Blueprint.Chevalley.Tag.F4 K)).trans QuotientGroup.quotientBot)) α hαord hout
  · obtain ⟨_, K, _, _, hK, ⟨e0⟩⟩ :=
      hX.chevalleyExceptionalModel (by simp [CFSG.Blueprint.chevalleyExceptionalTags])
    exact fixesSylowOutside_FE (Or.inr (Or.inl rfl)) hr hr2 hp hp5 hadm.2.1 hK
      (fun L _ _ => card_adjointGroup_untwisted (Or.inr (Or.inr (Or.inl rfl))) (K := L))
      (e0.trans ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot_field
          CFSG.Blueprint.Chevalley.Tag.E6 K)).trans QuotientGroup.quotientBot)) α hαord hout
  · obtain ⟨_, K, _, _, hK, ⟨e0⟩⟩ :=
      hX.chevalleyExceptionalModel (by simp [CFSG.Blueprint.chevalleyExceptionalTags])
    exact fixesSylowOutside_FE (Or.inr (Or.inr (Or.inl rfl))) hr hr2 hp hp5 hadm.2.1 hK
      (fun L _ _ => card_adjointGroup_untwisted (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (K := L))
      (e0.trans ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot_field
          CFSG.Blueprint.Chevalley.Tag.E7 K)).trans QuotientGroup.quotientBot)) α hαord hout
  · obtain ⟨_, K, _, _, hK, ⟨e0⟩⟩ :=
      hX.chevalleyExceptionalModel (by simp [CFSG.Blueprint.chevalleyExceptionalTags])
    exact fixesSylowOutside_FE (Or.inr (Or.inr (Or.inr rfl))) hr hr2 hp hp5 hadm.2.1 hK
      (fun L _ _ => card_adjointGroup_untwisted (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (K := L))
      (e0.trans ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot_field
          CFSG.Blueprint.Chevalley.Tag.E8 K)).trans QuotientGroup.quotientBot)) α hαord hout

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

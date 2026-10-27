module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6Tag
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitCyclicCore
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreSix
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.LieType.CurtisTits.TwistedE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional LayerSixE

namespace TwE6Nonsplit

section Model

theorem lieModel_twistedE6_of_mulEquiv_derivedCentralQuotient {f : ℕ} (hf : 1 ≤ f) {R : Type}
    [Group R]
    (e : R ≃* DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))) :
    LieModel R .twistedE6 0 2 f := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ TwistTag.E6.order := by
    rw [TwE6Toral.card_galoisField_two_mul f hf]
    rfl
  refine Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hf, rfl⟩, ?_⟩)
  exact ⟨GaloisField 2 (2 * f), inferInstance, inferInstance, hK, frobQ 2 f, frobQ_apply 2 f,
    ⟨e⟩⟩

theorem isQuasisimple_graphFixedRootGroup (f : ℕ) (hf : 1 ≤ f) :
    CFSG.IsQuasisimple ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)) := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    TwE6Toral.card_galoisField_two_mul f hf
  have hperf := (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hf
    (GaloisField 2 (2 * f)) hK (frobQ 2 f) (frobQ_apply 2 f)).2.2.1
  have h4 : 4 ≤ Nat.card (GaloisField 2 (2 * f)) := by
    rw [hK]
    have h2 : 2 ≤ 2 ^ f := by
      have := Nat.one_lt_two_pow (n := f) (by omega)
      omega
    nlinarith
  rw [← hperf]
  exact CFSG.LieType.Simplicity.isQuasisimple_derived_twistedFixedGroup
    (θ := frobQ 2 f) (frobQ_frobQ 2 f hf) h4

theorem markedModel_top_graphFixedRootGroup (f : ℕ) (hf : 1 ≤ f)
    {X : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hX : IsComponentOf X ⊤) :
    MarkedModel (⟨.twE6, 0, f⟩ : LargeEvenLabel)
      (↥X ⧸ Subgroup.center ↥X) := by
  haveI : Finite (↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :=
    Subtype.finite
  have hXtop := ExcNonsplit.eq_top_of_isComponentOf_top
    (isQuasisimple_graphFixedRootGroup f hf) hX
  subst hXtop
  obtain ⟨eD⟩ := nonempty_quotient_center_equiv_derivedCentralQuotient_ad f hf
  let E : (↥(⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))) ⧸ Subgroup.center ↥(⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * f)) (frobQ 2 f)))) ≃*
      (↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ⧸
        Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f))) :=
    QuotientGroup.congr _ _ Subgroup.topEquiv (Subgroup.map_center_eq Subgroup.topEquiv)
  show LieModel _ .twistedE6 0 2 f
  exact lieModel_twistedE6_of_mulEquiv_derivedCentralQuotient hf (E.trans eD)

theorem markedModel_top_twistedE6Group (f : ℕ) (hf : 1 ≤ f)
    {X : Subgroup (twistedE6Group 2 f)} (hX : IsComponentOf X ⊤) :
    MarkedModel (⟨.twE6, 0, f⟩ : LargeEvenLabel)
      (↥X ⧸ Subgroup.center ↥X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (twistedE6Group 2 f) := Subtype.finite
  have hQ : CFSG.IsQuasisimple (twistedE6Group 2 f) :=
    CFSG.LieType.CurtisTits.isQuasisimple_twistedE6 (p := 2) (f := f) hf
  have hXtop := ExcNonsplit.eq_top_of_isComponentOf_top hQ hX
  subst hXtop
  obtain ⟨eD⟩ := nonempty_quotient_center_equiv_derivedCentralQuotient_sc f hf
  let E : (↥(⊤ : Subgroup (twistedE6Group 2 f)) ⧸ Subgroup.center
      ↥(⊤ : Subgroup (twistedE6Group 2 f))) ≃*
      (twistedE6Group 2 f ⧸ Subgroup.center (twistedE6Group 2 f)) :=
    QuotientGroup.congr _ _ Subgroup.topEquiv (Subgroup.map_center_eq Subgroup.topEquiv)
  show LieModel _ .twistedE6 0 2 f
  exact lieModel_twistedE6_of_mulEquiv_derivedCentralQuotient hf (E.trans eD)

end Model

section Labels

theorem not_halfSplit_of_isComponentOf_top_ad {f : ℕ} (hf : 1 ≤ f) {p : ℕ}
    (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1)
    {X : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hX : IsComponentOf X ⊤) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hc : markChar lab = 2) (hM : MarkedModel lab (↥X ⧸ Subgroup.center ↥X)) {c : Prop} :
    ¬ LargeEvenHalfSplit p lab c := by
  have hmod := markedModel_top_graphFixedRootGroup f hf hX
  have hlab0 : LargeEvenInLambda2 (⟨.twE6, 0, f⟩ : LargeEvenLabel) := ⟨hf, rfl⟩
  have hGG : GGNbrNsTwE6Label p (⟨.twE6, 0, f⟩ : LargeEvenLabel) := ⟨rfl, hq1, hq2⟩
  exact NbrInnerMore.not_halfSplit_of_markedModel_twE6 hlab0 hGG hmod hlab hc hM c

theorem not_halfSplit_of_isComponentOf_top_sc {f : ℕ} (hf : 1 ≤ f) {p : ℕ}
    (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1)
    {X : Subgroup (twistedE6Group 2 f)} (hX : IsComponentOf X ⊤) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hc : markChar lab = 2)
    (hM : MarkedModel lab (↥X ⧸ Subgroup.center ↥X)) {c : Prop} :
    ¬ LargeEvenHalfSplit p lab c := by
  have hmod := markedModel_top_twistedE6Group f hf hX
  have hlab0 : LargeEvenInLambda2 (⟨.twE6, 0, f⟩ : LargeEvenLabel) := ⟨hf, rfl⟩
  have hGG : GGNbrNsTwE6Label p (⟨.twE6, 0, f⟩ : LargeEvenLabel) := ⟨rfl, hq1, hq2⟩
  exact NbrInnerMore.not_halfSplit_of_markedModel_twE6 hlab0 hGG hmod hlab hc hM c

end Labels

end TwE6Nonsplit

end CFSG.StandardType

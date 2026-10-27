module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLBridgeDefs
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaInnerDerived
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLOutsideTop
import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaInnerSU33
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerGroup
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.MarkingChevalley
import CFSG.RankThree.PartTwo.KFacts.AutSzOrderThree

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

private theorem largeEvenLabelAll_inn_pow_three_eq_one_twB2
    {lab : LargeEvenLabel} (ht : lab.tag = .twB2) :
    LargeEvenLabelAll lab fun _ _ I _ => ∀ s ∈ I, s ^ 3 = 1 → s = 1 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun s hs hs3 => ?_⟩
  obtain ⟨r, rfl⟩ := hs
  have h3 : ¬ 3 ∣ Nat.card (LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K)) := fun h =>
    CFSG.RankThree.PartTwo.KFacts.not_three_dvd_card_suzukiGroup hK
      (largeEvenSzGroup_eq ((n - 1) / 2) K ▸ h.trans (Subgroup.card_quotient_dvd_card _))
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hs3) with h1 | h3'
  · exact orderOf_eq_one_iff.1 h1
  · exact absurd (h3' ▸ (orderOf_map_dvd _ r).trans (orderOf_dvd_natCard r)) h3

private theorem not_isComponentOf_ggFix_of_fixSolvable {lab : LargeEvenLabel}
    (h : LargeEvenLabelAll lab (LargeEvenSimpleGuard fun _R _ I _ =>
      ∀ φ ∈ I, φ ≠ 1 → φ ^ 3 = 1 → Group.IsSolvable (ggFix φ))) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ s ∈ I, s ≠ 1 → s ^ 3 = 1 → ∀ J : Subgroup R, ¬ IsComponentOf J (ggFix s) :=
  h.mono fun _ _ _ _ h hs hna s hsI hs1 hs3 _ hJ =>
    Line63.H5.false_of_isComponentOf_of_isSolvable (h hs hna s hsI hs1 hs3) hJ

theorem largeEvenLabelAll_not_isComponentOf_ggFix_twB2_derived (hT : GGTitsThreeCentInput)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twB2 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ s ∈ I, s ≠ 1 → s ^ 3 = 1 → ∀ J : Subgroup R, ¬ IsComponentOf J (ggFix s) := by
  rcases htag with h | h | h | h
  · exact (largeEvenLabelAll_inn_pow_three_eq_one_twB2 h).mono
      fun _ _ _ _ h1 _ _ s hsI hs1 hs3 _ _ => hs1 (h1 s hsI hs3)
  · exact not_isComponentOf_ggFix_of_fixSolvable (LayerCyc.largeEvenLabelAll_fixSolvable_b2der h)
  · exact not_isComponentOf_ggFix_of_fixSolvable
      (largeEvenLabelAll_fixSolvable_G2der ggSU33ThreeCentInput_holds h)
  · exact not_isComponentOf_ggFix_of_fixSolvable (largeEvenLabelAll_fixSolvable_twF4der hT hlab h)

theorem ggTwE6OfOutsideAt_small (hT : GGTitsThreeCentInput) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twB2 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) :
    GGTwE6OfOutsideAt lab :=
  (CFSG.StandardType.largeEvenLabelAll_and
    (largeEvenLabelAll_not_isComponentOf_ggFix_twB2_derived hT hlab htag)
    (largeEvenLabelAll_not_ggOutsideInndiag_ggFix_one hlab)).mono
    fun _ _ _ _ ⟨h, h1⟩ hR hna _ s t _ hs3 _ _ hsI htI _ J₁ hJ₁ _ hout => by
      obtain rfl | hs1 := eq_or_ne s 1
      · exact (h1 hR hna t htI J₁ hJ₁ hout).elim
      · exact (h hR hna s hsI hs1 hs3 J₁ hJ₁).elim

theorem ggTwE6A5LAt_small (hT : GGTitsThreeCentInput) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twB2 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) :
    GGTwE6A5LAt lab :=
  (largeEvenLabelAll_not_isComponentOf_ggFix_twB2_derived hT hlab htag).mono
    fun _ _ _ _ h hR hna _ _ s _ hB hBI hsB hs1 _ _ J₁ hJ₁ _ _ =>
      (h hR hna s (hBI s hsB) hs1 (hB.2 s hsB) J₁ hJ₁).elim

end CFSG.StandardType.SCFourCover

end

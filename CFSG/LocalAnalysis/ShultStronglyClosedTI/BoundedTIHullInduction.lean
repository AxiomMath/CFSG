module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.TIInductionBase
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.StrongEmbeddingRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralInvolutionEmbeddingTransport

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFchapter1section1

theorem twoRankAtLeastTwo_iff_elementary_four (Y : Type) [Group Y] :
    TwoRankAtLeastTwo Y ↔ ∃ E : Subgroup Y, IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  constructor
  · rintro ⟨E, hcard, hsquare⟩
    have hinv (a : E) : a⁻¹ = a :=
      inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hsquare a)
    refine ⟨E, ⟨isMulCommutative_iff.mpr ?_, ?_⟩, hcard⟩
    · intro a b
      calc
        a * b = (a * b)⁻¹ := (hinv (a * b)).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by rw [hinv b, hinv a]
    · intro a ha
      exact congrArg E.subtype (hsquare ⟨a, ha⟩)
  · rintro ⟨E, hE, hcard⟩
    exact ⟨E, hcard, fun a => Subtype.ext (hE.2 a a.property)⟩

@[expose] def BoundedRankOneRecognition (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    (∃ E : Subgroup Y, IsElemAbelian 2 E ∧ Nat.card E = 4) →
      (∃ H : Subgroup Y, fusionStronglyEmbedded H) → R1Full Y

theorem bounded_rank_one_recognition
    (n : ℕ) : BoundedRankOneRecognition n := by
  intro Y _ _ _ hfour hstrong
  obtain ⟨H, hH⟩ := hstrong
  exact rank_two_strongEmbedding_r1Full
    ((twoRankAtLeastTwo_iff_elementary_four Y).mpr hfour) H hH

variable {G : Type} [Group G] [Finite G]

theorem bounded_quotient_hull_recognition (n : ℕ)
    (hFR : BoundedRankOneRecognition n) (hbound : Nat.card G ≤ n)
    (T : Sylow 2 G) (U : Subgroup G) (hUT : U ≤ (T : Subgroup G))
    (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U) (hcard : 4 ≤ Nat.card U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (x : Subgroup.center G) (horder : orderOf (x : G) = 2)
    (hB : fusionStronglyEmbedded
      ((Subgroup.normalizer
        (U.map (QuotientGroup.mk' (centralLiftKernel x)) : Set (G ⧸ centralLiftKernel x))).subgroupOf
        (Subgroup.normalClosure
          (U.map (QuotientGroup.mk' (centralLiftKernel x)) : Set (G ⧸ centralLiftKernel x))))) :
    let L := Subgroup.normalClosure (U : Set G)
    let K := L.map (QuotientGroup.mk' (centralLiftKernel x))
    IsQuasisimple K ∧ Subgroup.center K = oddCore K ∧
      Odd (Nat.card (Subgroup.center K)) ∧ fusionIsBenderGroup (K ⧸ Subgroup.center K) := by
  let Z := centralLiftKernel x
  let π := QuotientGroup.mk' Z
  let V := U.map π
  let K := Subgroup.normalClosure (V : Set (G ⧸ Z))
  let B := (Subgroup.normalizer (V : Set (G ⧸ Z))).subgroupOf K
  let W := V.subgroupOf K
  obtain ⟨_, _, _, _, hV, _, hVcard, _, _, _, himage, _, _, hquotient⟩ :=
    central_involution_quotient_datum T U hUT hU hUel hcard hclosed hTI hnormal x horder
  obtain ⟨hWB, hWnormal, hW, _, hWcard, hgen⟩ :=
    normalizer_elementary_ambient_hull_datum V hV hVcard hB
  have hrank : TwoRankAtLeastTwo K :=
    (twoRankAtLeastTwo_of_elementary_card_ge_four W hW hWcard).map_of_injective
      W.subtype W.subtype_injective
  have hKbound : Nat.card K < n :=
    lt_of_le_of_lt K.card_le_card_group (lt_of_lt_of_le hquotient hbound)
  have hrec := normal_elementary_hull_recognition B W hB hWB hWnormal hW hWcard hgen
    (hFR K hKbound ((twoRankAtLeastTwo_iff_elementary_four K).mp hrank) ⟨B, hB⟩)
  dsimp only at hrec ⊢
  rw [← himage]
  exact hrec

theorem strongly_closed_TI_embedding_from_local_criterion_and_smaller_recognition
    (n : ℕ) (_hn : 1 ≤ n) (hLC : BoundedInvolutionPointCriterion n)
    (hFR : BoundedRankOneRecognition n) :
    ∀ (G : Type) [Group G] [Finite G], Nat.card G ≤ n →
      ∀ (T : Sylow 2 G) (U : Subgroup G), U ≤ (T : Subgroup G) → U ≠ ⊥ →
        IsElemAbelian 2 U → fusionStronglyClosed (U : Set G) (T : Subgroup G) →
          fusionIsTI U → ¬ U.Normal →
            fusionStronglyEmbedded ((Subgroup.normalizer (U : Set G)).subgroupOf
              (Subgroup.normalClosure (U : Set G))) := by
  have hinduction : ∀ k : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = k →
      Nat.card G ≤ n →
      ∀ (T : Sylow 2 G) (U : Subgroup G), U ≤ (T : Subgroup G) → U ≠ ⊥ →
        IsElemAbelian 2 U → fusionStronglyClosed (U : Set G) (T : Subgroup G) →
          fusionIsTI U → ¬ U.Normal →
            fusionStronglyEmbedded ((Subgroup.normalizer (U : Set G)).subgroupOf
              (Subgroup.normalClosure (U : Set G))) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro G _ _ horder hbound T U hUT hU hUel hclosed hTI hnormal
      by_cases htwo : Nat.card U = 2
      · exact ti_induction_order_two_embedding T U hUT hU htwo hclosed hnormal
      have hcard := ti_induction_card_ge_four T U hUT hU htwo
      by_cases hcentral : ∃ c ∈ Subgroup.center G, orderOf c = 2
      · obtain ⟨c, hc, hcord⟩ := hcentral
        let x : Subgroup.center G := ⟨c, hc⟩
        let Z := centralLiftKernel x
        let π := QuotientGroup.mk' Z
        let V := U.map π
        let Q := T.mapSurjective (QuotientGroup.mk'_surjective Z)
        obtain ⟨_, _, hVQ, hVne, hV, _, _, hVclosed, hVTI, hVnormal,
          _, hpre, _, hsmaller⟩ :=
          central_involution_quotient_datum T U hUT hU hUel hcard hclosed hTI hnormal x hcord
        have hB := ih (Nat.card (G ⧸ Z)) (horder ▸ hsmaller)
          (G ⧸ Z) rfl (le_trans hsmaller.le hbound) Q V hVQ hVne hV
          hVclosed hVTI hVnormal
        obtain ⟨hquasi, _, _, hmodel⟩ := bounded_quotient_hull_recognition n hFR hbound
          T U hUT hU hUel hcard hclosed hTI hnormal x hcord hB
        obtain ⟨_, _, _, _, e, he⟩ := central_involution_hull_lifting
          T U hUT hUel hcard hclosed hTI x hcord hquasi hmodel
        exact central_involution_hull_embedding_transport U x e he hpre hB
      · have hno : ∀ c ∈ Subgroup.center G, orderOf c ≠ 2 := by
          intro c hc hcord
          exact hcentral ⟨c, hc, hcord⟩
        have hsmaller : SmallerTIHullEmbeddings.{0} (Nat.card G) := by
          intro Y _ _ hY Q W hWQ hWne hWel hWclosed hWTI hWnormal
          exact ih (Nat.card Y) (horder ▸ hY) Y rfl (le_trans hY.le hbound)
            Q W hWQ hWne hWel hWclosed hWTI hWnormal
        exact ti_induction_no_central_involution_embedding n hLC hbound
          T U hUT hU hUel hclosed hTI hnormal hno hsmaller
  intro G _ _ hbound
  exact hinduction (Nat.card G) G rfl hbound

end CFSG.ShultStronglyClosedTI

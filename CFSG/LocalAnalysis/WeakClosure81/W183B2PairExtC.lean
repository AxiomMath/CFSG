module

import CFSG.LocalAnalysis.WeakClosure81.W183B2PairExtA
import CFSG.LocalAnalysis.WeakClosure81.W183B2PairExtB
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem w183_map_inclusion_subgroupOf {X Y A : Subgroup G} (hXY : X ≤ Y) (hA : A ≤ X) :
    (A.subgroupOf X).map (Subgroup.inclusion hXY) = A.subgroupOf Y := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx)
  · intro hy
    have hyA : (y : G) ∈ A := Subgroup.mem_subgroupOf.1 hy
    exact ⟨⟨y, hA hyA⟩, Subgroup.mem_subgroupOf.2 hyA, rfl⟩

private theorem w183_card_image {P Q K M S : Subgroup G} [(K.subgroupOf (P ⊔ Q)).Normal]
    (hS : S ≤ P ⊔ Q) (hSp : IsPGroup 2 S) (hSK : S ⊓ K = S ⊓ M) :
    Nat.card ((S.subgroupOf (P ⊔ Q)).map (QuotientGroup.mk' (K.subgroupOf (P ⊔ Q)))) =
      2 ^ E3.mQuot S M := by
  rw [w183b2_card_image_mk]
  have h1 : (K.subgroupOf (P ⊔ Q)) ⊓ S.subgroupOf (P ⊔ Q) = (S ⊓ M).subgroupOf (P ⊔ Q) := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    have hx : (x : G) ∈ S ⊓ K ↔ (x : G) ∈ S ⊓ M := by rw [hSK]
    rw [Subgroup.mem_inf, Subgroup.mem_inf] at hx
    constructor
    · rintro ⟨hK', hS'⟩
      exact hx.1 ⟨hS', hK'⟩
    · intro h
      exact ⟨(hx.2 h).2, (hx.2 h).1⟩
  rw [h1, Subgroup.relIndex_subgroupOf hS, inf_comm, Subgroup.inf_relIndex_right]
  exact E3.relIndex_eq_two_pow hSp M

theorem w183b2_pq_data {P Q M₁ M₂ K : Subgroup G} [(K.subgroupOf (P ⊔ Q)).Normal]
    (hPe : IsElemAbelian 2 P) (hQe : IsElemAbelian 2 Q) (hPM : P ≤ M₁) (hQM : Q ≤ M₂)
    (hnot : ¬ Q ≤ M₁)
    (hK : (K : Set G) = ((Q ⊓ M₁ : Subgroup G) : Set G) * ((P ⊓ M₂ : Subgroup G) : Set G))
    (hconj : ∃ l ∈ P ⊔ Q, Q = conjSubgroup P l)
    {A B : Subgroup G} (hA : A ≤ P) (hB : B ≤ Q) :
    ∃ (π : ↥(A ⊔ B) →* (↥(P ⊔ Q) ⧸ K.subgroupOf (P ⊔ Q)))
      (P₁ P₂ : Subgroup (↥(P ⊔ Q) ⧸ K.subgroupOf (P ⊔ Q))),
      IsPGroup 2 π.ker ∧ IsElemAbelian 2 P₁ ∧ IsElemAbelian 2 P₂ ∧
      Nat.card P₁ = 2 ^ E3.mQuot P M₂ ∧ Nat.card P₂ = 2 ^ E3.mQuot P M₂ ∧
      E3.mQuot Q M₁ = E3.mQuot P M₂ ∧ P₁ ≠ P₂ ∧
      (A.subgroupOf (A ⊔ B)).map π ≤ P₁ ∧ (B.subgroupOf (A ⊔ B)).map π ≤ P₂ ∧
      Nat.card ((A.subgroupOf (A ⊔ B)).map π) = 2 ^ E3.mQuot A M₂ ∧
      Nat.card ((B.subgroupOf (A ⊔ B)).map π) = 2 ^ E3.mQuot B M₁ := by
  have hAB : A ⊔ B ≤ P ⊔ Q := sup_le (hA.trans le_sup_left) (hB.trans le_sup_right)
  have hPpG : IsPGroup 2 P := hPe.isPGroup
  have hQpG : IsPGroup 2 Q := hQe.isPGroup
  have hKpG : IsPGroup 2 K := w183b2_pq_isPGroup hPpG hQpG hK
  have hPK : P ⊓ K = P ⊓ M₂ := w183b2_pq_inf_left hQM hK
  have hQK : Q ⊓ K = Q ⊓ M₁ := w183b2_pq_inf_right hPM hK
  have hAK : A ⊓ K = A ⊓ M₂ := by
    ext x
    constructor
    · rintro ⟨hxA, hxK⟩
      have h1 : x ∈ P ⊓ K := ⟨hA hxA, hxK⟩
      rw [hPK] at h1
      exact ⟨hxA, h1.2⟩
    · rintro ⟨hxA, hxM⟩
      have h1 : x ∈ P ⊓ M₂ := ⟨hA hxA, hxM⟩
      rw [← hPK] at h1
      exact ⟨hxA, h1.2⟩
  have hBK : B ⊓ K = B ⊓ M₁ := by
    ext x
    constructor
    · rintro ⟨hxB, hxK⟩
      have h1 : x ∈ Q ⊓ K := ⟨hB hxB, hxK⟩
      rw [hQK] at h1
      exact ⟨hxB, h1.2⟩
    · rintro ⟨hxB, hxM⟩
      have h1 : x ∈ Q ⊓ M₁ := ⟨hB hxB, hxM⟩
      rw [← hQK] at h1
      exact ⟨hxB, h1.2⟩
  have hc1 := w183_card_image (P := P) (Q := Q) (K := K) (M := M₂)
    (le_sup_left : P ≤ P ⊔ Q) hPpG hPK
  have hc2 := w183_card_image (P := P) (Q := Q) (K := K) (M := M₁)
    (le_sup_right : Q ≤ P ⊔ Q) hQpG hQK
  have hcc := w183b2_pq_card_conj (P := P) (Q := Q) (K := K) hconj
  have hmQ : E3.mQuot Q M₁ = E3.mQuot P M₂ := by
    apply Nat.pow_right_injective (le_refl 2)
    show 2 ^ E3.mQuot Q M₁ = 2 ^ E3.mQuot P M₂
    rw [← hc2, hcc, hc1]
  have hmapA : (A.subgroupOf (A ⊔ B)).map
      ((QuotientGroup.mk' (K.subgroupOf (P ⊔ Q))).comp (Subgroup.inclusion hAB)) =
      (A.subgroupOf (P ⊔ Q)).map (QuotientGroup.mk' (K.subgroupOf (P ⊔ Q))) := by
    rw [← Subgroup.map_map, w183_map_inclusion_subgroupOf hAB le_sup_left]
  have hmapB : (B.subgroupOf (A ⊔ B)).map
      ((QuotientGroup.mk' (K.subgroupOf (P ⊔ Q))).comp (Subgroup.inclusion hAB)) =
      (B.subgroupOf (P ⊔ Q)).map (QuotientGroup.mk' (K.subgroupOf (P ⊔ Q))) := by
    rw [← Subgroup.map_map, w183_map_inclusion_subgroupOf hAB le_sup_right]
  refine ⟨(QuotientGroup.mk' (K.subgroupOf (P ⊔ Q))).comp (Subgroup.inclusion hAB),
    (P.subgroupOf (P ⊔ Q)).map (QuotientGroup.mk' (K.subgroupOf (P ⊔ Q))),
    (Q.subgroupOf (P ⊔ Q)).map (QuotientGroup.mk' (K.subgroupOf (P ⊔ Q))), ?_, ?_, ?_, ?_, ?_,
    hmQ, w183b2_pq_ne hPM hnot hK, ?_, ?_, ?_, ?_⟩
  · let π : ↥(A ⊔ B) →* ↥(P ⊔ Q) ⧸ K.subgroupOf (P ⊔ Q) :=
      (QuotientGroup.mk' (K.subgroupOf (P ⊔ Q))).comp (Subgroup.inclusion hAB)
    have hmem : ∀ y : ↥π.ker, ((A ⊔ B).subtype.comp π.ker.subtype) y ∈ K := by
      intro y
      have h1 : π y.1 = 1 := MonoidHom.mem_ker.1 y.2
      have h2 : Subgroup.inclusion hAB y.1 ∈ K.subgroupOf (P ⊔ Q) :=
        (QuotientGroup.eq_one_iff _).1 h1
      exact Subgroup.mem_subgroupOf.1 h2
    have hinj : Function.Injective
        (((A ⊔ B).subtype.comp π.ker.subtype).codRestrict K hmem) := by
      intro a b hab
      have h1 : (((a : ↥π.ker) : ↥(A ⊔ B)) : G) = (((b : ↥π.ker) : ↥(A ⊔ B)) : G) :=
        congrArg (fun z : ↥K => (z : G)) hab
      exact Subtype.val_injective (Subtype.val_injective h1)
    exact IsPGroup.of_injective hKpG _ hinj
  · exact (hPe.subgroupOf (P ⊔ Q)).map _
  · exact (hQe.subgroupOf (P ⊔ Q)).map _
  · exact hc1
  · rw [hcc]
    exact hc1
  · rw [hmapA]
    exact Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.2
      (hA (Subgroup.mem_subgroupOf.1 hx)))
  · rw [hmapB]
    exact Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.2
      (hB (Subgroup.mem_subgroupOf.1 hx)))
  · rw [hmapA]
    exact w183_card_image (P := P) (Q := Q) (K := K) (M := M₂) (hA.trans le_sup_left)
      (hPpG.to_le hA) hAK
  · rw [hmapB]
    exact w183_card_image (P := P) (Q := Q) (K := K) (M := M₁) (hB.trans le_sup_right)
      (hQpG.to_le hB) hBK

end CFSG.LocalAnalysis.WeakClosure81

end

module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupU3Setting
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupNormalQuasisimple

public section

namespace CFSG.LocalAnalysis.WeakClosure81.InFGroupU3

open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase
open scoped commutatorElement

variable {Q : Type} [Group Q] [Finite Q] {C : Subgroup Q} {n : ℕ}

private theorem solvableRadicalSubgroupOf_le_center (h : Setting C n) :
    ((CFSG.solvableRadical ↥(⊤ : Subgroup Q)).map (⊤ : Subgroup Q).subtype).subgroupOf C ≤
      center ↥C := by
  set R : Subgroup Q := (CFSG.solvableRadical ↥(⊤ : Subgroup Q)).map (⊤ : Subgroup Q).subtype
  haveI : R.Normal :=
    (inferInstance : (CFSG.solvableRadical ↥(⊤ : Subgroup Q)).Normal).map _
      (fun q => ⟨⟨q, Subgroup.mem_top q⟩, rfl⟩)
  haveI : (R.subgroupOf C).Normal := inferInstance
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top h.quasisimple
    (R.subgroupOf C) with hle | htop
  · exact hle
  · exfalso
    have hCR : C ≤ R := Subgroup.subgroupOf_eq_top.mp htop
    haveI : Group.IsSolvable ↥(CFSG.solvableRadical ↥(⊤ : Subgroup Q)) :=
      CFSG.ABGLocalTools.solvableRadical_isSolvable
    haveI : Group.IsSolvable ↥R :=
      Group.isSolvable_of_surjective
        (MonoidHom.subgroupMap_surjective (⊤ : Subgroup Q).subtype
          (CFSG.solvableRadical ↥(⊤ : Subgroup Q)))
    have hCs : Group.IsSolvable ↥C :=
      Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hCR).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hCR).surjective
    haveI : Group.IsPerfect ↥C := Group.isPerfect_def.mpr h.quasisimple.1
    haveI : Nontrivial (↥C ⧸ center ↥C) := h.quasisimple.2.toNontrivial
    haveI : Nontrivial ↥C := (QuotientGroup.mk'_surjective (center ↥C)).nontrivial
    exact Group.IsPerfect.not_isSolvable ↥C hCs

private theorem act_eq_one_of_forall_commutator_mem (h : Setting C n) {g : Q}
    (hg : ∀ y ∈ C,
      ⁅g, y⁆ ∈ (CFSG.solvableRadical ↥(⊤ : Subgroup Q)).map (⊤ : Subgroup Q).subtype) :
    h.act g = 1 := by
  haveI := h.normal
  have hle := solvableRadicalSubgroupOf_le_center h
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H y =>
    have hC : ⁅g, (y : Q)⁆ ∈ C := by
      rw [commutatorElement_def]
      exact C.mul_mem (h.normal.conj_mem _ y.2 g) (C.inv_mem y.2)
    have hcen : (⟨⁅g, (y : Q)⁆, hC⟩ : ↥C) ∈ center ↥C :=
      hle (Subgroup.mem_subgroupOf.mpr (hg y y.2))
    have hfix : h.act g (QuotientGroup.mk y) = QuotientGroup.mk y :=
      (UCK.Odd.actHom_mk_eq_iff C g y.2).mpr
        ((UCK.Odd.mem_center_iff_mem_centerOf C ⟨⁅g, (y : Q)⁆, hC⟩).mp hcen)
    simpa using hfix

theorem Setting.solvableRadical_le_center (h : Setting C n) :
    (CFSG.solvableRadical ↥(⊤ : Subgroup Q)).map (⊤ : Subgroup Q).subtype ≤
      (center ↥C).map C.subtype := by
  set R : Subgroup Q := (CFSG.solvableRadical ↥(⊤ : Subgroup Q)).map (⊤ : Subgroup Q).subtype
  haveI : R.Normal :=
    (inferInstance : (CFSG.solvableRadical ↥(⊤ : Subgroup Q)).Normal).map _
      (fun q => ⟨⟨q, Subgroup.mem_top q⟩, rfl⟩)
  intro r hr
  refine h.mem_center_of_act_eq_one (act_eq_one_of_forall_commutator_mem h fun y _ => ?_)
  have hconj : y * r⁻¹ * y⁻¹ ∈ R := by
    simpa using (inferInstance : R.Normal).conj_mem r⁻¹ (R.inv_mem hr) y
  have hmem : r * (y * r⁻¹ * y⁻¹) ∈ R := R.mul_mem hr hconj
  simpa only [commutatorElement_def, mul_assoc] using hmem

theorem Setting.inCalEi_top (h : Setting C n) {T A : Subgroup Q} (hT : IsSylowIn 2 T ⊤)
    (hA : CFSG.Open.IsElemAbelian 2 A) (hA1 : A ≠ ⊥) (hcard : Nat.card A ≤ 2 ^ n) :
    InCalEi n T A ⊤ := by
  have hoddZ : Odd (Nat.card ((center ↥C).map C.subtype)) := by
    rw [Subgroup.card_map_of_injective (K := center ↥C) (f := C.subtype)
      (fun _ _ hxy => Subtype.ext hxy)]
    exact h.odd_center
  have hoddR : Odd (Nat.card ↥(CFSG.solvableRadical ↥(⊤ : Subgroup Q))) := by
    rw [← Subgroup.card_map_of_injective
      (K := CFSG.solvableRadical ↥(⊤ : Subgroup Q)) (f := (⊤ : Subgroup Q).subtype)
      (fun _ _ hxy => Subtype.ext hxy)]
    exact Odd.of_dvd_nat hoddZ (Subgroup.card_dvd_of_le h.solvableRadical_le_center)
  have hR : E1.IsTwoClosed (CFSG.solvableRadical ↥(⊤ : Subgroup Q)) := by
    refine ⟨⊥, ⟨bot_le, IsPGroup.of_card (n := 0) (by simp), ?_⟩, ?_⟩
    · rw [Subgroup.relIndex_bot_left]
      exact Odd.not_two_dvd_nat hoddR
    · rw [Subgroup.bot_subgroupOf]
      infer_instance
  have hAJ : ∃ a ∈ A, ∃ x ∈ C,
      ⁅a, x⁆ ∉ (CFSG.solvableRadical ↥(⊤ : Subgroup Q)).map (⊤ : Subgroup Q).subtype := by
    by_contra hcon
    have hcon' : ∀ a ∈ A, ∀ x ∈ C,
        ⁅a, x⁆ ∈ (CFSG.solvableRadical ↥(⊤ : Subgroup Q)).map (⊤ : Subgroup Q).subtype := by
      intro a ha x hx
      by_contra hmem
      exact hcon ⟨a, ha, x, hx, hmem⟩
    have hAZ : A ≤ (center ↥C).map C.subtype := by
      intro a ha
      exact h.mem_center_of_act_eq_one
        (act_eq_one_of_forall_commutator_mem h fun y hy => hcon' a ha y hy)
    have hoddA : Odd (Nat.card A) :=
      Odd.of_dvd_nat hoddZ (Subgroup.card_dvd_of_le hAZ)
    haveI : Subsingleton ↥A :=
      CFSG.GH74.Generic.eq_bot_of_isPGroup_two_of_odd hA.isPGroup hoddA
    exact hA1 (Subgroup.eq_bot_of_subsingleton A)
  refine ⟨⟨le_inf (E1.tauOf_le ⊤ T A) le_top, ?_, ?_, Or.inr ?_⟩, ?_⟩
  · rw [inf_top_eq]
    exact CFSG.ABGLocalTools.isSylowOf_iff.mpr hT
  · rw [h.pCoreOf_top_eq_bot]
    exact fun hle => hA1 (le_bot_iff.mp hle)
  · exact eCaseII_of_normal_quasisimple le_top (h.normal.subgroupOf ⊤) h.quasisimple
      (fun x _ => h.two_quot x) hR le_top hAJ
  · rw [h.pCoreOf_top_eq_bot]
    have hpow : 2 ^ E3.mQuot A (⊥ : Subgroup Q) = Nat.card A := by
      rw [← E3.relIndex_eq_two_pow hA.isPGroup (⊥ : Subgroup Q), Subgroup.relIndex_bot_left]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (hpow.symm ▸ hcard)

end CFSG.LocalAnalysis.WeakClosure81.InFGroupU3

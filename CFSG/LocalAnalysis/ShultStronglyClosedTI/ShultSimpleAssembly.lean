module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.BoundedTIHullInduction

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFchapter1section1

universe u

theorem shult_nonabelian_simple_center_eq_bot {Y : Type u} [Group Y]
    [IsSimpleGroup Y] (hnonab : ∃ a b : Y, a * b ≠ b * a) :
    Subgroup.center Y = ⊥ := by
  rcases (inferInstance : (Subgroup.center Y).Normal).eq_bot_or_eq_top with hbot | htop
  · exact hbot
  · obtain ⟨a, b, hab⟩ := hnonab
    exact (hab ((Subgroup.center_eq_top_iff.mp htop).is_comm.comm a b)).elim

theorem shult_simple_model_of_top_center_quotient {Y : Type u} [Group Y]
    [IsSimpleGroup Y] (hnonab : ∃ a b : Y, a * b ≠ b * a)
    (hmodel : fusionIsBenderGroup
      ((⊤ : Subgroup Y) ⧸ Subgroup.center (⊤ : Subgroup Y))) :
    fusionIsBenderGroup Y := by
  let e : (⊤ : Subgroup Y) ≃* Y := Subgroup.topEquiv
  have hcenter : (Subgroup.center (⊤ : Subgroup Y)).map e.toMonoidHom = ⊥ := by
    have hhom : e.toMonoidHom = (e : (⊤ : Subgroup Y) →* Y) := by
      ext x
      rfl
    rw [hhom]
    rw [Subgroup.map_center_eq, shult_nonabelian_simple_center_eq_bot hnonab]
  let q : ((⊤ : Subgroup Y) ⧸ Subgroup.center (⊤ : Subgroup Y)) ≃* (Y ⧸ ⊥) :=
    QuotientGroup.congr (Subgroup.center (⊤ : Subgroup Y)) ⊥ e hcenter
  exact rankOneModel_of_equiv (q.trans QuotientGroup.quotientBot).symm hmodel

theorem shult_simple_from_bounded_local_criterion
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hLC : BoundedInvolutionPointCriterion (Nat.card G))
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (T : Sylow 2 G) (U : Subgroup G) (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥)
    (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) : fusionIsBenderGroup G := by
  obtain ⟨hnormal, hhull⟩ := ti_simple_elementary_hull hnonab U hU hUel
  obtain ⟨hcard, _, _⟩ := ti_simple_rank_and_odd_core hnonab T U hUT hU hUel hclosed
  have hB := strongly_closed_TI_embedding_from_local_criterion_and_smaller_recognition
    (Nat.card G) Nat.card_pos hLC (bounded_rank_one_recognition (Nat.card G))
    G le_rfl T U hUT hU hUel hclosed hTI hnormal
  have hmodel := (normalizer_elementary_ambient_hull_native_recognition U hUel hcard hB).2.2.2
  rw [hhull] at hmodel
  exact shult_simple_model_of_top_center_quotient hnonab hmodel

end CFSG.ShultStronglyClosedTI

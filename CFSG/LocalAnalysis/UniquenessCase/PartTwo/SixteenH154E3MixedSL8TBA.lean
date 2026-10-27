module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.B15P4

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_sl28_cover_exists (D : Data G) (S : s16h_Std D) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L)
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    ∃ L₀ L₁ : Subgroup G, L₀ ∈ calC D.M ∧ L₁ ∈ calC D.M ∧ L₀ ≠ L₁ ∧
      barSub ⊥ V h.hyp151.isElemAbelian L₀ = lBar ⊥ V h.hyp151.isElemAbelian L ∧
      barSub ⊥ V h.hyp151.isElemAbelian L₁ =
        barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) := by
  have hV := h.hyp151.isElemAbelian
  have h125 := h.hyp16.hyp125
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  obtain ⟨L₀, hL₀, hL₀bar⟩ :=
    exists_calC_cover_of_component (D := D) (V₀ := ⊥) (V := V) h125 S.h127 S.h119 hcomp
  have ha : (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹ ∈ Mbar D.M ⊥ V hV :=
    (Mbar D.M ⊥ V hV).inv_mem (actTil_mem_barSub ⊥ V hV hxM (hMs hxM))
  have hcomp' := isComponentOf_map_equiv
    (MulAut.conj (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹) hcomp
  have hMbar_fix : (Mbar D.M ⊥ V hV).map
      (MulAut.conj (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹).toMonoidHom = Mbar D.M ⊥ V hV :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer ha)
  rw [hMbar_fix] at hcomp'
  have hLbx : barSub ⊥ V hV (conjSubgroup L x) =
      (lBar ⊥ V hV L).map (MulAut.conj (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹).toMonoidHom :=
    s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hxM) L
  rw [← hLbx] at hcomp'
  obtain ⟨L₁, hL₁, hL₁bar⟩ :=
    exists_calC_cover_of_component (D := D) (V₀ := ⊥) (V := V) h125 S.h127 S.h119 hcomp'
  refine ⟨L₀, L₁, hL₀, hL₁, ?_, hL₀bar, hL₁bar⟩
  intro heq
  have hLb_eq : (lBar ⊥ V hV L).map
      (MulAut.conj (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹).toMonoidHom = lBar ⊥ V hV L := by
    rw [← hLbx, ← hL₁bar, ← heq, hL₀bar]
  have hnorm : (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹ ∈
      normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 hLb_eq
  have hnorm' : actTil ⊥ V hV ⟨x, hMs hxM⟩ ∈
      normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) := by
    have := (normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV)))).inv_mem hnorm
    simpa using this
  exact hxn ((mem_preBarSub D.M ⊥ V hV
    (normalizer (barSub ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))))).2
      ⟨hxM, hMs hxM, hnorm'⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

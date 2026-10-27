module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveHyp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open scoped Pointwise

theorem fourFive_quotQuot_equiv {Q : Type} [Group Q] (N : Subgroup Q) [N.Normal]
    (Y' : Subgroup (Q ⧸ N)) [Y'.Normal] :
    ∃ e : ((Q ⧸ N) ⧸ Y') ≃* (Q ⧸ Y'.comap (QuotientGroup.mk' N)),
      ∀ T : Subgroup Q,
        ((T.map (QuotientGroup.mk' N)).map (QuotientGroup.mk' Y')).map e.toMonoidHom =
          T.map (QuotientGroup.mk' (Y'.comap (QuotientGroup.mk' N))) := by
  let Y : Subgroup Q := Y'.comap (QuotientGroup.mk' N)
  have hmap : Y.map (QuotientGroup.mk' N) = Y' := by
    dsimp only [Y]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Y'
  have hNY : N ≤ Y := by
    dsimp only [Y]
    exact QuotientGroup.le_comap_mk' N Y'
  let e : ((Q ⧸ N) ⧸ Y') ≃* (Q ⧸ Y) :=
    (QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient N Y hNY)
  refine ⟨e, ?_⟩
  intro T
  have hcomp : e.toMonoidHom.comp ((QuotientGroup.mk' Y').comp (QuotientGroup.mk' N)) =
      QuotientGroup.mk' Y := by
    ext q
    change e (QuotientGroup.mk' Y' (QuotientGroup.mk' N q)) = QuotientGroup.mk' Y q
    simp only [e, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
      QuotientGroup.quotientQuotientEquivQuotient_apply_mk, QuotientGroup.mk'_apply]
  change ((T.map (QuotientGroup.mk' N)).map (QuotientGroup.mk' Y')).map e.toMonoidHom =
    T.map (QuotientGroup.mk' Y)
  rw [Subgroup.map_map, Subgroup.map_map, MonoidHom.comp_assoc, hcomp]

theorem fourFive_quotCompFAS_quotient {j : ℕ} {Q : Type} [Group Q] [Finite Q] {T : Subgroup Q}
    (N : Subgroup Q) [N.Normal] (h : fourFiveQuotCompFAS j Q T) :
    fourFiveQuotCompFAS j (Q ⧸ N) (T.map (QuotientGroup.mk' N)) := by
  intro Y' hY'
  obtain ⟨e, he⟩ := fourFive_quotQuot_equiv N Y'
  have hY := h (Y'.comap (QuotientGroup.mk' N)) (Subgroup.normal_comap _)
  have h' := fourFive_compFAS_mulEquiv (j := j) e.symm hY
  have hcancel : ∀ X : Subgroup ((Q ⧸ N) ⧸ Y'),
      (X.map e.toMonoidHom).map e.symm.toMonoidHom = X := by
    intro X
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hmap : (T.map (QuotientGroup.mk' (Y'.comap (QuotientGroup.mk' N)))).map
      e.symm.toMonoidHom = (T.map (QuotientGroup.mk' N)).map (QuotientGroup.mk' Y') := by
    rw [← he T]
    exact hcancel _
  simpa only [hmap] using h'

theorem fourFive_compFAS_of_quotCompFAS {j : ℕ} {Q : Type} [Group Q] [Finite Q] {T : Subgroup Q}
    (h : fourFiveQuotCompFAS j Q T) : fourFiveCompFAS j Q T := by
  have hbot := h ⊥ (by infer_instance)
  have h' := fourFive_compFAS_mulEquiv (j := j) (QuotientGroup.quotientBot (G := Q)) hbot
  have hcomp : (QuotientGroup.quotientBot (G := Q)).toMonoidHom.comp
      (QuotientGroup.mk' (⊥ : Subgroup Q)) = MonoidHom.id Q := by
    ext x
    rfl
  have hmap : (T.map (QuotientGroup.mk' (⊥ : Subgroup Q))).map
      (QuotientGroup.quotientBot (G := Q)).toMonoidHom = T := by
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  simpa only [hmap] using h'

end CFSG.LocalAnalysis.WeakClosure81

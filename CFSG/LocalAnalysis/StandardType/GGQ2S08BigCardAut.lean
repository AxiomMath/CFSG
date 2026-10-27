module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open Module

theorem ggQ2s08_card_automizer_le {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {lab : LargeEvenLabel} (hlab : GGQ2S08BigLabel lab)
    (hMW : GGQ2LabelWeyl lab M.coxeter) :
    Nat.card ↥(ggAutomizer L Bs) ≤ 2 ^ lab.rank * lab.rank.factorial := by
  have hα : ∀ i, M.root i (M.coroot i) = (2 : ZMod 3) := by
    intro i
    rw [M.pairing i i, M.isCartan.1 i]
    norm_num
  have hlin : ∀ i, ggLin (p := 3) M.model (M.simple i) = reflection (hα i) := fun i =>
    ggLin_eq_reflection M.model (hα i) (M.simple_apply i)
  have hφL : M.coxeter.IsLiftable M.simple := by
    intro i j
    apply ggLin_injective (p := 3) M.model
    rw [map_pow, map_mul, hlin i, hlin j, map_one]
    exact isLiftable_reflection_of_intCartan M.isCartan M.coroot M.root hα M.pairing i j
  set Φ : M.coxeter.Group →* MulAut ↥Bs :=
    M.coxeter.toCoxeterSystem.lift ⟨M.simple, hφL⟩ with hΦ
  have hsimple : ∀ i, Φ (M.coxeter.toCoxeterSystem.simple i) = M.simple i := fun i => by
    rw [hΦ, CoxeterSystem.lift_apply_simple]
  have hcomp : (⇑Φ) ∘ M.coxeter.toCoxeterSystem.simple = M.simple := funext hsimple
  have hrange : Φ.range = ggAutomizer L Bs := by
    rw [M.automizer_L, MonoidHom.range_eq_map,
      ← M.coxeter.toCoxeterSystem.subgroup_closure_range_simple, MonoidHom.map_closure,
      ← Set.range_comp, hcomp]
  have hfix : GGIsWeylMatrixFixed M.coxeter := by
    obtain ⟨-, htag, hrank⟩ := hlab
    rcases htag with htag | htag | htag | htag | htag
    · obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
          M.coxeter = (CoxeterMatrix.A lab.rank).reindex e := by
        simpa [GGQ2LabelWeyl, htag] using hMW
      exact Or.inl ⟨lab.rank, e, by omega, Or.inl he⟩
    · obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
          M.coxeter = (CoxeterMatrix.B lab.rank).reindex e := by
        simpa [GGQ2LabelWeyl, htag] using hMW
      exact Or.inl ⟨lab.rank, e, by omega, Or.inr (Or.inl ⟨by omega, he⟩)⟩
    · obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
          M.coxeter = (CoxeterMatrix.B lab.rank).reindex e := by
        simpa [GGQ2LabelWeyl, htag] using hMW
      exact Or.inl ⟨lab.rank, e, by omega, Or.inr (Or.inl ⟨by omega, he⟩)⟩
    · obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
          M.coxeter = (ggCoxeterMatrixD lab.rank).reindex e := by
        simpa [GGQ2LabelWeyl, htag] using hMW
      exact Or.inl ⟨lab.rank, e, by omega, Or.inr (Or.inr ⟨by omega, he⟩)⟩
    · obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
          M.coxeter = (ggCoxeterMatrixD lab.rank).reindex e := by
        simpa [GGQ2LabelWeyl, htag] using hMW
      exact Or.inl ⟨lab.rank, e, by omega, Or.inr (Or.inr ⟨by omega, he⟩)⟩
  have hFT : TauCeti.IsFiniteType M.cartan :=
    isFiniteType_of_ggIsWeylMatrixFixed hfix M.isCartan
  have hfin : Finite M.coxeter.Group := by
    rw [← coxeterMatrix_eq_of_ggIntCartan hFT M.isCartan]
    exact CFSG.LieType.RootSystem.finite_group hFT
  haveI := hfin
  have hcard : Nat.card ↥(ggAutomizer L Bs) ≤ Nat.card M.coxeter.Group := by
    rw [← hrange]
    exact Nat.card_le_card_of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  have hcard_cox : Nat.card M.coxeter.Group ≤ 2 ^ lab.rank * lab.rank.factorial := by
    obtain ⟨-, htag, hrank⟩ := hlab
    rcases htag with htag | htag | htag | htag | htag
    · obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
          M.coxeter = (CoxeterMatrix.A lab.rank).reindex e := by
        simpa [GGQ2LabelWeyl, htag] using hMW
      exact l05nK3a_card_reindex_le (CoxeterMatrix.A lab.rank) e he
        (l05nK3a_coxeterA_le lab.rank)
    · obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
          M.coxeter = (CoxeterMatrix.B lab.rank).reindex e := by
        simpa [GGQ2LabelWeyl, htag] using hMW
      exact l05nK3a_card_reindex_le (CoxeterMatrix.B lab.rank) e he (card_coxeterB_le lab.rank)
    · obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
          M.coxeter = (CoxeterMatrix.B lab.rank).reindex e := by
        simpa [GGQ2LabelWeyl, htag] using hMW
      exact l05nK3a_card_reindex_le (CoxeterMatrix.B lab.rank) e he (card_coxeterB_le lab.rank)
    · obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
          M.coxeter = (ggCoxeterMatrixD lab.rank).reindex e := by
        simpa [GGQ2LabelWeyl, htag] using hMW
      exact l05nK3a_card_reindex_le (ggCoxeterMatrixD lab.rank) e he
        (l05nK3a_coxeterD_le lab.rank (by omega))
    · obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
          M.coxeter = (ggCoxeterMatrixD lab.rank).reindex e := by
        simpa [GGQ2LabelWeyl, htag] using hMW
      exact l05nK3a_card_reindex_le (ggCoxeterMatrixD lab.rank) e he
        (l05nK3a_coxeterD_le lab.rank (by omega))
  exact hcard.trans hcard_cox

end CFSG.StandardType

end

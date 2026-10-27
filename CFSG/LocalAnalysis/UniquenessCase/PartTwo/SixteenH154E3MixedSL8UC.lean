module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8TBA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8TBB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_sl28_cover_gen (D : Data G) (S : s16h_Std D) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    ∃ L₀ L₁ X : Subgroup G,
      L₀ ∈ calC D.M ∧ L₁ ∈ calC D.M ∧ L₀ ≠ L₁ ∧
      IsL2 (Bar2 L₀) 3 ∧ IsL2 (Bar2 L₁) 3 ∧ pCoreOf 2 L₀ ≠ ⊥ ∧ L₀ ≤ D.M ∧
      L₀ ≤ centralizer (wSub ⊥ V h.hyp151.isElemAbelian L : Set G) ∧
      (X : Set G) = (L₀ : Set G) * (L₁ : Set G) ∧ D.M ≤ normalizer (X : Set G) ∧
      barSub ⊥ V h.hyp151.isElemAbelian L₀ =
        barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) := by
  obtain ⟨K₀, K₁, hK₀, hK₁, hne, hK₀bar, hK₁bar⟩ :=
    s16h_e3_sl28_cover_exists D S h hcomp hxM hxn
  refine ⟨K₁, K₀, K₁ ⊔ K₀, hK₁, hK₀, hne.symm, ?_, ?_, ?_, hK₁.1.le, ?_, ?_, ?_, hK₁bar⟩
  · exact s16h_e3_sl28_cover_bar2_isL2 D S h hrow hxM hxn hK₁ (Or.inr hK₁bar)
  · exact s16h_e3_sl28_cover_bar2_isL2 D S h hrow hxM hxn hK₀ (Or.inl hK₀bar)
  · exact s16h_e3_sl28_cover_pCore D hK₁
      (s16h_e3_sl28_cover_bar2_isL2 D S h hrow hxM hxn hK₁ (Or.inr hK₁bar))
  · exact s16h_e3_sl28_cover_cent D h hxM hxn hK₁ hK₁bar
  · exact Subgroup.coe_mul_of_right_le_normalizer_left K₁ K₀
      (calC_le_normalizer_of_ne hK₁ hK₀ hne.symm)
  · exact s16h_e3_sl28_cover_normal D h hcomp hs2 hxM hxn hK₁ hK₀ hne.symm hK₁bar hK₀bar

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

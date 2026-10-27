module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA1A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA1BA
public import CFSG.Goldschmidt.Steps.G55Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_z_noncyclic
    (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (h7 : 7 ∈ D.sig)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) :
    ∀ w ∈ wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G), w ≠ 1 →
      ∃ E : Subgroup G, E ≤ D.M ∧ IsPGroup 7 E ∧ ¬ IsCyclic ↥E ∧
        E ≤ Subgroup.centralizer ({w} : Set G) := by
  intro w hw _hw1
  have hV := h.hyp151.isElemAbelian
  set Z : Subgroup G := wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) with hZdef
  have hZx : conjSubgroup Z x = Z := by
    rw [hZdef]
    exact s16h_sl28_conj_z_eq D h hs2 hxM hxn hZ0
  have hZL : Z ≤ Subgroup.centralizer (L : Set G) := by
    rw [hZdef]; exact inf_le_right
  have hLZ : L ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.le_centralizer_iff.2 hZL
  have hLxZ : conjSubgroup L x ≤ Subgroup.centralizer (Z : Set G) := by
    calc conjSubgroup L x
        ≤ conjSubgroup (Subgroup.centralizer (Z : Set G)) x :=
          E3.conjSubgroup_mono_left x hLZ
      _ = Subgroup.centralizer (conjSubgroup Z x : Set G) := E3.conjSubgroup_centralizer Z x
      _ = Subgroup.centralizer (Z : Set G) := by rw [hZx]
  have hsupZ : L ⊔ conjSubgroup L x ≤ Subgroup.centralizer (Z : Set G) := sup_le hLZ hLxZ
  have hwZ : w ∈ Z := by rw [hZdef]; exact hw
  have hsupw : L ⊔ conjSubgroup L x ≤ Subgroup.centralizer ({w} : Set G) :=
    hsupZ.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hwZ))
  have hLxM : conjSubgroup L x ≤ D.M := by
    have h1 : conjSubgroup L x ≤ conjSubgroup D.M x :=
      E3.conjSubgroup_mono_left x h.hyp151.le
    rwa [conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hxM)] at h1
  have hsupM : L ⊔ conjSubgroup L x ≤ D.M := sup_le h.hyp151.le hLxM
  have hrank : 2 ≤ CFSG.Open.pRank 7 (L ⊔ conjSubgroup L x) :=
    s16h_sl28_seven_sup_pRank_two D h hrow hxM hxn
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨E, hEjoin, hEab, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 7) (k := 2) hrank
  refine ⟨E, hEjoin.trans hsupM, hEab.isPGroup, ?_, hEjoin.trans hsupw⟩
  refine CFSG.Goldschmidt.G55.not_isCyclic_of_isElemAbelian (p := 7) (by norm_num) hEab ?_
  rw [hEcard]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

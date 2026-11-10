module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2Equiv
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.Adapters.LieModelSimple
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem ncard_conjSet_barSub_le {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {L : Subgroup G} (hLM : L ≤ D.M) :
    (conjSet (barSub V₀ V hV.isElemAbelian L)
        (Mbar D.M V₀ V hV.isElemAbelian)).ncard ≤ (conjSetOf D.M L).ncard := by
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀
  have hLS : L ≤ stabTil V₀ V := hLM.trans hMS
  have hsub : conjSet (barSub V₀ V hV.isElemAbelian L)
      (Mbar D.M V₀ V hV.isElemAbelian) ⊆
      barSub V₀ V hV.isElemAbelian '' conjSetOf D.M L := by
    rintro X ⟨n, hn, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV.isElemAbelian D.M n).1 hn
    refine ⟨L.map (MulAut.conj (g : G)).toMonoidHom, ⟨(g : G), hg, rfl⟩, ?_⟩
    exact TwelveTwentyThree.barSub_map_conj hV.isElemAbelian hLS g.2
  calc
    (conjSet (barSub V₀ V hV.isElemAbelian L)
        (Mbar D.M V₀ V hV.isElemAbelian)).ncard
        ≤ (barSub V₀ V hV.isElemAbelian '' conjSetOf D.M L).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (conjSetOf D.M L).ncard := Set.ncard_image_le (Set.toFinite _)

abbrev Shape18_6 (D : Data G) (L : Subgroup G) : Prop :=
  (UC22.conjClosure D.M L ≠ L ∧
      (IsL2 (Bar2 L) (S17.nOf L) ∨ IsSz (Bar2 L) (S17.nOf L)) ∧
      2 < S17.nOf L ∧ (conjSetOf D.M L).ncard = 2) ∨
    (UC22.conjClosure D.M L = L ∧
      ((IsL2 (Bar2 L) (S17.nOf L) ∧ 2 < S17.nOf L ∧ ∃ k : ℕ, S17.nOf L = 2 ^ k) ∨
        (IsU5 (Bar2 L) 2 ∧ S17.nOf L = 2) ∨
        (Odd (S17.nOf L) ∧ 1 < S17.nOf L ∧
          (IsSp4 (Bar2 L) (S17.nOf L) ∨ IsG2 (Bar2 L) (S17.nOf L))) ∨
        (1 < S17.nOf L ∧ IsU4 (Bar2 L) (S17.nOf L))))

section Certified


theorem w4Hyp18_6_cases {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L)
    (hLb : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥)
    (hshape : Shape18_6 D L) :
    (((IsL2 ↥(barSub V₀ V h.hyp125.isElemAbelian L) (S17.nOf L) ∨
        IsSz ↥(barSub V₀ V h.hyp125.isElemAbelian L) (S17.nOf L)) ∧
      2 < S17.nOf L ∧
      (conjSet (barSub V₀ V h.hyp125.isElemAbelian L)
        (Mbar D.M V₀ V h.hyp125.isElemAbelian)).ncard ≤ 2) ∨
    (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) =
        barSub V₀ V h.hyp125.isElemAbelian L ∧ S17.nOf L = 2 ∧
      CFSG.Blueprint.LieModel ↥(barSub V₀ V h.hyp125.isElemAbelian
          (UC22.conjClosure D.M L)) .PSU 5 2 2) ∨
    (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) =
        barSub V₀ V h.hyp125.isElemAbelian L ∧ Odd (S17.nOf L) ∧ 1 < S17.nOf L ∧
      (IsSp4 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) (S17.nOf L) ∨
        IsG2 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) (S17.nOf L))) ∨
    (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) =
        barSub V₀ V h.hyp125.isElemAbelian L ∧ 1 < S17.nOf L ∧
      IsU4 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) (S17.nOf L))) := by
  have hLc : L ∈ calC D.M := h.hL.1
  have equivOf (hs : IsSimpleGroup (Bar2 L)) :
      Nonempty (Bar2 L ≃* ↥(barSub V₀ V h.hyp125.isElemAbelian L)) :=
    barSubBar2Equiv_of_isSimpleGroup h.hyp125 hLc hLb hs
  have hcard_le : (conjSet (barSub V₀ V h.hyp125.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp125.isElemAbelian)).ncard ≤ (conjSetOf D.M L).ncard :=
    ncard_conjSet_barSub_le h.hyp125 hLc.1.le
  rcases hshape with ⟨-, hL2Sz, hn2, hc2⟩ | ⟨hXL, hrest⟩
  ·
    refine Or.inl ⟨?_, hn2, hcard_le.trans (le_of_eq hc2)⟩
    have hs : IsSimpleGroup (Bar2 L) := by
      rcases hL2Sz with hL2 | hSz
      · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
      · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity (Bar2 L) 2 (S17.nOf L)
          (CFSG.Blueprint.LieModel.suzukiModel hSz).2).2
    obtain ⟨e⟩ := equivOf hs
    rcases hL2Sz with hL2 | hSz
    · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hL2)
    · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e hSz)
  ·
    rw [hXL]
    have hcard_one : (conjSetOf D.M L).ncard = 1 := uc22p2214_ncard_eq_one_of_eq hXL.symm
    rcases hrest with ⟨hL2, hn2, -⟩ | ⟨hU5, hn2⟩ | ⟨hodd, hn1, hSpG2⟩ | ⟨hn1, hU4⟩
    ·
      refine Or.inl ⟨?_, hn2, ?_⟩
      · obtain ⟨e⟩ := equivOf
          (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2)
        exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hL2)
      · calc
          (conjSet (barSub V₀ V h.hyp125.isElemAbelian L)
              (Mbar D.M V₀ V h.hyp125.isElemAbelian)).ncard
              ≤ (conjSetOf D.M L).ncard := hcard_le
          _ = 1 := hcard_one
          _ ≤ 2 := by norm_num
    ·
      refine Or.inr (Or.inl ⟨rfl, hn2, ?_⟩)
      obtain ⟨e⟩ := equivOf
        (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU5)
      exact CFSG.Blueprint.LieModel.of_mulEquiv e hU5
    ·
      refine Or.inr (Or.inr (Or.inl ⟨rfl, hodd, hn1, ?_⟩))
      have hs : IsSimpleGroup (Bar2 L) := by
        rcases hSpG2 with hSp | hG2
        · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp
        · exact (CFSG.LieType.Simplicity.fam_g2_simplicity (Bar2 L) 2 (S17.nOf L)
            (CFSG.Blueprint.LieModel.chevalleyExceptionalModel hG2 (by decide))).2
      obtain ⟨e⟩ := equivOf hs
      rcases hSpG2 with hSp | hG2
      · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hSp)
      · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e hG2)
    ·
      refine Or.inr (Or.inr (Or.inr ⟨rfl, hn1, ?_⟩))
      obtain ⟨e⟩ := equivOf
        (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4)
      exact CFSG.Blueprint.LieModel.of_mulEquiv e hU4

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

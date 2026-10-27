module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx.RestBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx.RestSl2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Surj
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.GL2Max
import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx

open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3 (SL3 A0 GL2NonsplitMax)

set_option linter.unusedSectionVars false

theorem oddIdxRest_sl3_isCyclic {F : Type} [Field F] [Finite F] (hq : Nat.card F % 3 = 2)
    (X : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) (hX : IsPGroup 3 X) : IsCyclic X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ¬ 3 ∣ Nat.card F := by omega
  have h31 : ¬ 3 ∣ Nat.card F - 1 := by omega
  have hcyc : IsCyclic ↥(X.map Matrix.SpecialLinearGroup.toGL) :=
    CFSG.SectionRank.OddCover.isCyclic_of_isPGroup_GL_three h3 h31
      (hX.map Matrix.SpecialLinearGroup.toGL)
  exact (X.equivMapOfInjective Matrix.SpecialLinearGroup.toGL
    Matrix.SpecialLinearGroup.toGL_injective).isCyclic.mpr hcyc

theorem oddIdxNone_sl3_of_five_le {F : Type} [Field F] [Finite F]
    (hq : Nat.card F % 3 = 2) (h5 : 5 ≤ Nat.card F) (hne : Nat.card F ≠ 5) :
    OddIdxNone (Matrix.SpecialLinearGroup (Fin 3) F) := by
  intro N Y D hN hodd hD hDY hYN hnorm hY hNK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : ∀ X : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F),
      IsPGroup 3 X → IsCyclic X := fun X hX => oddIdxRest_sl3_isCyclic hq X hX
  obtain ⟨g, hg⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves.exists_conj_eq_of_card_eq_three
      hcyc hD CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.card_A0
  set W : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
    N.map (MulAut.conj g).toMonoidHom with hW
  have hNW : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ W := by
    rw [hg, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hnorm
  have hNns : ¬ Group.IsSolvable ↥N := oddIdx_not_isSolvable hYN hY
  have hWns : ¬ Group.IsSolvable ↥W := by
    intro hs
    apply hNns
    haveI : Group.IsSolvable ↥W := hs
    set e := N.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hKW : CFSG.KCore.KGroupNonab (DvdOrThreeFree 51840) ↥W :=
    CFSG.KCore.KGroupNonab.of_mulEquiv (isoInvariant_dvdOrThreeFree 51840) hNK
      (N.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  obtain ⟨W₁, hW₁, φ, hφ⟩ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.index_cases_SL3_surj
      hq h5 (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.gl2NonsplitMax hq h5)
      hNW hWns
  rcases oddIdxRest_card_of_sl2_section hW₁ (by omega) (by omega) φ hφ hKW with h4 | h5'
  · omega
  · exact hne h5'

theorem oddIdxNone_sl3_card_two {F : Type} [Field F] [Finite F] (h2 : Nat.card F = 2) :
    OddIdxNone (Matrix.SpecialLinearGroup (Fin 3) F) := by
  intro N Y D hN hodd hD hDY hYN hnorm hY hNK
  have h5Y : 5 ∣ Nat.card Y := oddIdx_five_dvd_card hY
  have h5N : 5 ∣ Nat.card N := h5Y.trans (Subgroup.card_dvd_of_le hYN)
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = 168 := by
    haveI := Fintype.ofFinite F
    rw [Matrix.card_SL_field, Fin.prod_univ_three, ← Nat.card_eq_fintype_card, h2]
    norm_num
  have h5G : 5 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) :=
    h5N.trans (Subgroup.card_subgroup_dvd_card N)
  rw [hcard] at h5G
  norm_num at h5G

theorem oddIdxProp_psl3_rest {K : Type} [Group K] [Finite K]
    {p f : ℕ} (hrest : 2 ≤ f ∨ p = 2) (hq : p ^ f % 3 = 2) (hL : LieModel K .PSL 3 p f) :
    OddIdxProp K := by
  apply oddIdxProp_of_none
  obtain ⟨F, hFld, hFfin, hFcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  letI := hFld
  haveI := hFfin
  have hq' : Nat.card F % 3 = 2 := by rw [hFcard]; exact hq
  let eS : K ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    e.trans
      ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 F).symm.trans
        (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.pslEquivSL3 hq'))
  by_cases h2 : Nat.card F = 2
  · exact oddIdxNone_of_mulEquiv eS (oddIdxNone_sl3_card_two h2)
  · refine oddIdxNone_of_mulEquiv eS (oddIdxNone_sl3_of_five_le hq' ?_ ?_)
    · have h2le : 2 ≤ Nat.card F := by
        have := Finite.one_lt_card (α := F)
        omega
      omega
    · intro h5eq
      have hpf : p ^ f = 5 := by rw [← hFcard]; exact h5eq
      obtain ⟨hp5, hf1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_five).mp hpf
      rcases hrest with hf2 | hp2
      · omega
      · omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineAdjRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaPlusFourSquare
public import CFSG.RankThree.PartTwo.Sec15.Sylow155Center

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16low_pRank_le_one_of_isSLn_two
    {X : Type} [Group X] [Finite X] {a : ℕ}
    (ha : a = 2 ∨ a = 3) (hshape : IsSLn X 2 a)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 1 := by
  have ha2 : 2 ≤ a := by omega
  exact pRank_le_one_of_isL2_or_isSz
    (Or.inl (CFSG.GroupTheory.isL2_of_isSLn_two ha2 hshape)) hq hq2

theorem s16low_pRank_le_one_of_isSpn_two
    {X : Type} [Group X] [Finite X] {a : ℕ}
    (ha : a = 2 ∨ a = 3) (hshape : IsSpn X 2 a)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 1 := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hshape
  let := hKf
  let := hKfin
  obtain ⟨e2⟩ :=
    CFSG.RankThree.GF2n.Stroth80.nonempty_statedSp_one_mulEquiv_statedSL_two K
  have hdiv : (2 : ℕ) / 2 = 1 := by norm_num
  have he : X ≃* ↥(StatedSp 1 K) := by simpa [hdiv] using e
  have hSL : IsSLn X 2 a := ⟨K, hKf, hKfin, hKcard, ⟨he.trans e2⟩⟩
  exact s16low_pRank_le_one_of_isSLn_two ha hSL hq hq2

theorem s16low_pRank_le_one_of_isOmegaMinus_four
    {X : Type} [Group X] [Finite X] {a : ℕ}
    (ha : a = 2 ∨ a = 3) (hshape : IsOmegaMinus X 4 a)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 1 := by
  have ha1 : 1 ≤ a := by omega
  exact pRank_le_one_of_isL2_or_isSz
    (Or.inl (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.isL2_of_isOmegaMinus_four ha1 hshape))
    hq hq2

theorem s16low_false_of_isQuasisimple_isOmegaPlus_four
    {X : Type} [Group X] {a : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (ha : a = 2 ∨ a = 3)
    (hshape : IsOmegaPlus X 4 a) :
    False := by
  have ha2 : 2 ≤ a := by omega
  obtain ⟨A, B, hAg, hBg, ⟨e⟩, hLA, hLB⟩ := isL2Square_of_isOmegaPlus ha2 hshape
  let := hAg
  let := hBg
  have hSA : StatedClassicalModel A .PSL 2 2 a :=
    (isL2_iff_statedClassicalModel (X := A) (a := a)).1 hLA
  have hSB : StatedClassicalModel B .PSL 2 2 a :=
    (isL2_iff_statedClassicalModel (X := B) (a := a)).1 hLB
  have hntA : Nontrivial A :=
    (CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two hSA).toNontrivial
  have hntB : Nontrivial B :=
    (CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two hSB).toNontrivial
  have hqAssembly : CFSG.Assembly.IsQuasisimple X :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open X).mpr hq
  have hqNative : CFSG.IsQuasisimple X :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).mp hqAssembly
  exact CFSG.RankThree.PartTwo.Sec15.Sylow155T.false_of_mulEquiv_prod hqNative hntA hntB e

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

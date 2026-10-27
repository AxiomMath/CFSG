module

public import CFSG.Models.PGL
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
public import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.PGLModel

open CFSG.Assembly.LowTwoRank

theorem isSimpleGroup_projSL_of_two_le {n : ℕ} (K : Type) [Field K] (hn : 2 ≤ n)
    (h22 : n ≠ 2 ∨ Nat.card K ≠ 2) (h23 : n ≠ 2 ∨ Nat.card K ≠ 3) :
    IsSimpleGroup (projSL n K) := by
  have := CFSG.BenderSuzuki.External.huppert_II_6_13 (K := K) n hn h22 h23
  exact ((projSLEquivStatedProj n K).trans
    (projectiveSpecialLinearGroupEquivStatedProj n K).symm).isSimpleGroup

theorem isSimpleGroup_projSU_of_admissible {n p f : ℕ} [Fact p.Prime]
    (hadm : StatedLieAdmissible .PSU n p f) : IsSimpleGroup (projSU n p f) :=
  (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ n p f
    (statedClassicalModel_of_mulEquiv_projSU hadm (MulEquiv.refl _))).2

end CFSG.PGLModel

namespace CFSG.Open.StatedAPI

open CFSG.Assembly.LowTwoRank

theorem isSimpleGroup_statedProj_statedSL {d : ℕ} (K : Type) [Field K] (hd : 2 ≤ d)
    (h22 : d ≠ 2 ∨ Nat.card K ≠ 2) (h23 : d ≠ 2 ∨ Nat.card K ≠ 3) :
    IsSimpleGroup (StatedProj (StatedSL d K)) := by
  have := CFSG.BenderSuzuki.External.huppert_II_6_13 (K := K) d hd h22 h23
  exact (projectiveSpecialLinearGroupEquivStatedProj d K).symm.isSimpleGroup

end CFSG.Open.StatedAPI

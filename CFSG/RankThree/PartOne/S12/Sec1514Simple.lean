module

public import CFSG.RankThree.PartOne.S12.Sec1514Defs
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.Adapters.RankTwoModelTransports
import CFSG.Models.PGLSimple
public import CFSG.Assembly.GL83LieDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.RankThreeEven (projImage projSL projSp projOmegaMinus)
open CFSG.Assembly.LowTwoRank

theorem isSimpleGroup_projSL_four (K : Type) [Field K] : IsSimpleGroup (projSL 4 K) :=
  CFSG.PGLModel.isSimpleGroup_projSL_of_two_le K (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))

theorem isSimpleGroup_projSp_three (K : Type) [Field K] [Finite K] : IsSimpleGroup (projSp 3 K) := by
  have h2 : 1 < Nat.card K := Finite.one_lt_card
  have h : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ 3) ∨ (Nat.card K = 2 ∧ 3 ≤ 3) := by
    rcases (show Nat.card K = 2 ∨ Nat.card K = 3 ∨ 4 ≤ Nat.card K by omega) with h | h | h
    · exact Or.inr (Or.inr ⟨h, le_rfl⟩)
    · exact Or.inr (Or.inl ⟨h, by norm_num⟩)
    · exact Or.inl (Or.inr h)
  have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 3 (by norm_num) h
  exact (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk (StatedSp 3 K)).symm.isSimpleGroup

theorem isSimpleGroup_projOmegaMinus_three (K : Type) [Field K] [Finite K] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : IsSimpleGroup (projOmegaMinus 3 K b c) := by
  have := CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus
    (n := 4) (K := K) (b := b) (c := c) (by norm_num) hirr
  exact (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk
    (StatedOmega (StatedQuadMinus 4 K b c))).symm.isSimpleGroup

theorem isSimpleGroup_of_lieRow {G : Type} [Group G] {r p : ℕ} {I : Subgroup G} (hr1 : 1 ≤ r)
    (hr4 : r ≤ 4) (h : LieRow r p I) : IsSimpleGroup ↥I := by
  interval_cases r
  · obtain ⟨f, -, -, ⟨e⟩⟩ := h
    have := isSimpleGroup_projSL_four (GaloisField 2 f)
    exact e.isSimpleGroup
  · obtain ⟨f, -, -, ⟨e⟩⟩ := h
    have := isSimpleGroup_projSp_three (GaloisField 2 f)
    exact e.isSimpleGroup
  · obtain ⟨f, -, -, b, c, hirr, ⟨e⟩⟩ := h
    have := isSimpleGroup_projOmegaMinus_three (GaloisField 2 f) b c hirr
    exact e.isSimpleGroup
  · obtain ⟨f, -, -, b, c, hirr, ⟨e⟩⟩ := h
    have := isSimpleGroup_projOmegaMinus_three (GaloisField 2 f) b c hirr
    exact e.isSimpleGroup

theorem lieRow_of_outcome {G : Type} [Group G] {p : ℕ} {E A I : Subgroup G} (h : Outcome152 p E A I)
    (hEA : E = A) : ∃ r : ℕ, 1 ≤ r ∧ r ≤ 4 ∧ LieRow r p I := by
  rcases h with h1 | h2 | h3 | h4 | h5
  · obtain ⟨f, h1f, hpf, hom, -⟩ := h1
    exact ⟨1, le_rfl, by norm_num, f, h1f, hpf, hom⟩
  · obtain ⟨f, h1f, hpf, hom, -⟩ := h2
    exact ⟨2, by norm_num, by norm_num, f, h1f, hpf, hom⟩
  · obtain ⟨f, h1f, hpf, hom, -⟩ := h3
    exact ⟨3, by norm_num, by norm_num, f, h1f, hpf, hom⟩
  · obtain ⟨f, h1f, hpf, hom, -⟩ := h4
    exact ⟨4, by norm_num, le_rfl, f, h1f, hpf, hom⟩
  · obtain ⟨_, -, -, -, -, -, hne, -⟩ := h5
    exact absurd hEA hne

end CFSG.RankThree.PartOne

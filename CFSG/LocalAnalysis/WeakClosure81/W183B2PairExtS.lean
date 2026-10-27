module

import CFSG.GH74.SmallRanks.PSL
import CFSG.Blueprint.LieModelAPI
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsSz)

theorem w183b2_shape_of_quotShape {Lb : Type} [Group Lb] [Finite Lb]
    {d : ℕ}
    (h : ((∃ r : ℕ, IsL2 Lb r) ∨ (∃ r : ℕ, IsSz Lb r) ∨
        (∃ m : ℕ, Odd m ∧ Nonempty (Lb ≃* DihedralGroup m))) ∧ twoRank Lb = d) :
    IsL2 Lb d ∨ IsSz Lb d ∨ ∃ m : ℕ, Odd m ∧ Nonempty (Lb ≃* DihedralGroup m) := by
  obtain ⟨hshape, hrank⟩ := h
  rcases hshape with ⟨r, hr⟩ | ⟨r, hr⟩ | hdih
  · have hrk : twoRank Lb = r :=
      CFSG.GH74.SmallRanks.twoRank_eq_of_statedClassicalModel_PSL_two_two
        (hr.statedClassicalModel (by decide))
    have hrd : r = d := hrk.symm.trans hrank
    subst hrd
    exact Or.inl hr
  · obtain ⟨-, hsz⟩ := CFSG.Blueprint.LieModel.suzukiModel hr
    obtain ⟨-, a, ha, F, _, _, hf, hF, ⟨e⟩⟩ := hsz
    have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hf]
    have hrk : twoRank Lb = 2 * a + 1 :=
      CFSG.ShultStronglyClosedTI.SuzukiModel.twoRank_eq_of_mulEquiv hF' e
    have hrd : r = d := by rw [hf, ← hrk, hrank]
    subst hrd
    exact Or.inr (Or.inl hr)
  · exact Or.inr (Or.inr hdih)

end CFSG.LocalAnalysis.WeakClosure81

end

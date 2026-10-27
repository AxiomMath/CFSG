module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFourteenB
public import CFSG.LocalAnalysis.WeakClosure81.NineDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.Timmesfeld75 (IsTI)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem hyp125_inCalV {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hne : V₀ ≠ ⊥) : InCalV D.M V₀ := by
  rcases h.1 with ⟨-, hbot⟩ | ⟨h0, -, -⟩
  · exact absurd hbot hne
  · exact h0.1

theorem hyp125_isTI {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hne : V₀ ≠ ⊥) : IsTI V₀ := by
  rcases h.1 with ⟨-, hbot⟩ | ⟨h0, -, -⟩
  · exact absurd hbot hne
  · exact h0.2.2.2.1

theorem hyp125_centralizer_le {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hne : V₀ ≠ ⊥) {z : G} (hz : z ∈ D.T) (hzc : ∀ t ∈ D.T, z * t = t * z) (hz1 : z ≠ 1) :
    centralizer ({z} : Set G) ≤ D.M := by
  rcases h.1 with ⟨-, hbot⟩ | ⟨-, hcu, -⟩
  · exact absurd hbot hne
  · exact (hcu z hz hzc hz1).1

theorem hyp9_of_hyp125 (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (h8 : 8 ≤ Nat.card V₀) : Hyp9 V₀ D.T := by
  have hne : V₀ ≠ ⊥ := by
    rintro rfl
    simp at h8
  have hW : InCalV D.M V₀ := hyp125_inCalV h hne
  have hTI : IsTI V₀ := hyp125_isTI h hne
  exact
    { hyp7 := TwelveSeven.hyp7_of_inCalV D hW hTI h8
      sylow := by
        rw [normalizer_eq_of_inCalV D hW]
        exact TwelveShort.isSylowIn_of_le D D.sylowM.le
      ne := (TwelveFourteen.wClos_zero_ne_self hTim hcat D hW hTI (by omega)).symm
      rk_gt := TwelveSeven.two_lt_rk_of_card hW.2.2.2 h8 }

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

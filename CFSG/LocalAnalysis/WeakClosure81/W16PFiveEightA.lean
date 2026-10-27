module

public import CFSG.LocalAnalysis.WeakClosure81.W15SixB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem IsPairAt.conjClosure_sup_kerMOf_eq {M X A : Subgroup G} (h : IsPairAt M X A)
    (hA : IsElemAbelian 2 A) : conjClosure A X ⊔ kerMOf M X = X := by
  have hNX : conjClosure A X ≤ X :=
    conjClosure_le fun g hg z hz => X.mul_mem (X.mul_mem hg (h.A_le hz)) (X.inv_mem hg)
  have hKX : kerMOf M X ≤ X := kerMOf_le_group M X
  refine le_antisymm (sup_le hNX hKX) ?_
  by_contra hle
  have hne : conjClosure A X ⊔ kerMOf M X ≠ X := fun heq => hle heq.ge
  have hYM : conjClosure A X ⊔ kerMOf M X ≤ M :=
    h.le_M_of_proper (sup_le hNX hKX) hne ((le_conjClosure A X).trans le_sup_left) le_sup_right
  have hNM : conjClosure A X ≤ M := le_sup_left.trans hYM
  have hNnorm : ((conjClosure A X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 (le_normalizer_conjClosure A X)
  exact h.not_le_ker ((le_conjClosure A X).trans (le_kerMOf_of_normal hNX hNnorm hNM))

end CFSG.LocalAnalysis.WeakClosure81

end

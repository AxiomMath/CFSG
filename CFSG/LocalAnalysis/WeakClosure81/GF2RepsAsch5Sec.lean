module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20b
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (InEGroup)

theorem cfShape_quotient {K : Type} [Group K] {P : ∀ (X : Type) [Group X], Prop}
    (N : Subgroup K) [N.Normal] (h : CFShape K P) : CFShape (K ⧸ N) P :=
  fun L _ hL hnc =>
    h L (CFSG.Quasithin.H13.L829N.isCompositionFactor_of_surjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) hL) hnc

theorem cfShape_of_isSolvable {K : Type} [Group K] [Group.IsSolvable K]
    (P : ∀ (X : Type) [Group X], Prop) : CFShape K P := by
  intro L _ hL hnc
  obtain ⟨a, b, hab⟩ := hnc
  exact absurd
    (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20b_simpSec_comm
      (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20b_simpSec_of_cf hL) a b) hab

end CFSG.LocalAnalysis.WeakClosure81

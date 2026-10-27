module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoSyl
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_T_sup {D : Data G} {L : Subgroup G} (hLM : L ≤ D.M) :
    CFSG.Quasithin.IsSylowIn 2 D.T (L ⊔ D.T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : CFSG.Quasithin.IsSylowIn 2 D.T D.M :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 D.sylowM
  exact CFSG.LocalAnalysis.WeakClosure81.isSylowIn_of_le_of_le hTsyl le_sup_right
    (sup_le hLM D.sylowM.le)

theorem isSylowIn_barSub_T_sup {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hLM : L ≤ D.M) :
    CFSG.Quasithin.IsSylowIn 2 (barSub V₀ V h.isElemAbelian D.T)
      (barSub V₀ V h.isElemAbelian (L ⊔ D.T)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : L ⊔ D.T ≤ stabTil V₀ V := (sup_le hLM D.sylowM.le).trans
    (le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀)
  have h1 : CFSG.ABGLocalTools.IsSylowOf 2 (D.T.subgroupOf (stabTil V₀ V))
      ((L ⊔ D.T).subgroupOf (stabTil V₀ V)) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (stabTil V₀ V),
      Subgroup.map_subgroupOf_eq_of_le (le_sup_right.trans hK),
      Subgroup.map_subgroupOf_eq_of_le hK]
    exact CFSG.ABGLocalTools.isSylowOf_iff.2 (isSylowIn_T_sup hLM)
  exact CFSG.ABGLocalTools.isSylowOf_iff.1
    (s16c7_isSylowOf_map h1 (actTil V₀ V h.isElemAbelian))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

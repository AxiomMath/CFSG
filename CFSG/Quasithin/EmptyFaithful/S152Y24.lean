module

public import CFSG.Quasithin.EmptyFaithful.S152Y02

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

theorem yOf152_le_M {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}
    (hs : Setting152 T Mc M) : yOf152 T Mc M ≤ M := by
  have hTM : T ≤ M := hs.mf.1.1.2
  have hRM : rcOf Mc M ≤ M := (pCoreOf_le 2 _).trans inf_le_right
  refine (oTwoUpper_le _).trans (conjClosure_le fun g hg z hz => ?_)
  have hgM : g ∈ M := sup_le ((oTwoUpper_le _).trans (S152Y.m0Of_le T Mc M)) hTM hg
  exact M.mul_mem (M.mul_mem hgM (hRM hz)) (M.inv_mem hgM)

end CFSG.Quasithin

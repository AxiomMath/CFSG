module

public import CFSG.Quasithin.Vol2.Ch3T325Q
public import CFSG.Quasithin.Vol2.Ch3T325L

public section

namespace CFSG.Quasithin.H13.T325

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem inf_centralizer_VM_eq_bot (h4 : Vol2.Ch11.TmpL6_3_2_2_four)
    (hC : V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) ⊓
      Subgroup.centralizer (L : Set G) = ⊥ := by
  have h := (h4 G T L V₀ c.fsu).1
  rw [c.fsuCVM_eq] at h
  change _ = conjClosure (V₀ ⊓ Subgroup.centralizer (conjClosure L T : Set G))
    (Subgroup.normalizer (conjClosure L T : Set G)) at h
  rw [c.eqL, hC, conjClosure_bot] at h
  exact h

end Ctx

end CFSG.Quasithin.H13.T325

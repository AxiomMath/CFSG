module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFa
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFw

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

namespace Conf4212

variable {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
include c

open scoped IsMulCommutative in
theorem ff_of_case2_alt
    (halt : IsAltNaturalSection (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) ⁅reducedAggregate (L ⊔ T), L⁆
      ⊥ ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)) 8) :
    ∃ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
      IsFFModule (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
        (autOn (L ⊔ T) ⁅reducedAggregate (L ⊔ T), L⁆) :=
  c.ff_of_autOn_LHR fun _ => FFa.isFFModule_autOn_of_altNatural halt FFa.isFFModule_heart8

open scoped IsMulCommutative in
theorem ff_of_altBlock6
    (hCV : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hblk : IsAltBlockType (perfectCore (L ⊓ H)) 6) :
    ∃ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
      IsFFModule (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
        (autOn (L ⊔ T) ⁅reducedAggregate (L ⊔ T), L⁆) := by
  have hVZ : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓
      Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) = ⊥ := by
    rw [← c.inf_centralizer_eq]
    exact hCV
  have := c.isMulCommutative_V
  have hFF := FFa.isFFModule_autOn_of_altBlock hblk c.V_le_blockU c.LH_le_normalizer_V
    c.hypC28.V_ne hVZ
  refine ⟨this, B1Red.isFFModule_mono ?_ hFF⟩
  exact T4213N.autOn_le_of_acts c.sup_le_normalizer_V fun a ha =>
    ⟨a, (((perfectCore_le _).trans inf_le_left).trans le_sup_left) ha, fun _ _ => rfl⟩

end Conf4212

end CFSG.Quasithin.H13.Ch4

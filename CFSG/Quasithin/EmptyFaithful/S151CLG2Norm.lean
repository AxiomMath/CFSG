module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBNorm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBOrd
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp

public section

namespace CFSG.Quasithin.CLG2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.Quasithin.GoldMLB CFSG.Quasithin.H13.VolI

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

theorem not_a38Types_image_of_rankTwoOrder
    {X L : Subgroup G} (hLX : L ≤ X)
    (hrk : RankTwoOrder (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L))) :
    ¬ A38Types ↥((L.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) := by
  intro hA
  have hS := isSimpleGroup_of_a38Types hA
  have hord := a38Order_card hA
  set π : ↥X →* ↥X ⧸ CFSG.pCore 2 ↥X := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  set ρ₀ : ↥L →* ↥X ⧸ CFSG.pCore 2 ↥X := π.comp (Subgroup.inclusion hLX) with hρ₀
  have hrange : ρ₀.range = (L.subgroupOf X).map π := by
    rw [hρ₀, MonoidHom.range_comp, Subgroup.inclusion_range]
  rw [← hrange] at hA hS hord
  have hker2 : IsPGroup 2 ρ₀.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict, hρ₀, ← MonoidHom.comap_ker, hπ, QuotientGroup.ker_mk']
    exact (CFSG.pCore_isPGroup (G := ↥X) (p := 2)).comap_of_injective _
      (Subgroup.inclusion_injective hLX)
  have hne : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≠ 1 := by
    intro h1
    exact rankTwoOrder_ne_one hrk h1
  have hcard := card_eq_of_simple_image hS ρ₀.rangeRestrict ρ₀.rangeRestrict_surjective hker2 hne
  rw [hcard] at hord
  exact a38Order_not_rankTwoOrder hord hrk

theorem g1_le_normalizer_of_rankTwoOrder
    (h38 : A38ForSQTK) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hcomp : IsComponentOf L (g1_1516 Z₁))
    (hrk : RankTwoOrder (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L))) :
    g1_1516 Z₁ ≤ Subgroup.normalizer (L : Set G) := by
  have hLX : L ≤ g1_1516 Z₁ := hc.hL.mem.1
  have hLcomp : L ∈ cComp (g1_1516 Z₁) :=
    Id2519.mem_cComp_of_isComponentIn (DoubleA3.isComponentIn_iff_open.mpr hcomp)
  have hsqtk : IsSQTKIn (g1_1516 Z₁) := hc.h18.five.2.2.sqtk
  exact normalizes_of_not_a38 h38 hsqtk hLcomp (not_a38Types_image_of_rankTwoOrder hLX hrk)

end CFSG.Quasithin.CLG2

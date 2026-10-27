module

public import CFSG.Quasithin.EmptyFaithful.S151ZH
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBNorm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma33
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
public import CFSG.Quasithin.EmptyFaithful.S151XF

public section

namespace CFSG.Quasithin.S151S9U

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem a38Types_image_iff {G : Type} [Group G] [Finite G] {X L : Subgroup G}
    (hL : L ∈ cComp X) :
    A38Types ↥((L.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) ↔
      A38Types (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨e⟩ := modO2_mulEquiv hL
  exact ⟨A38Types.of_mulEquiv e.symm, A38Types.of_mulEquiv e⟩

theorem not_a38Types_image_of_sporadic (kN : SporadicSixNotA38) {G : Type} [Group G] [Finite G]
    {X L : Subgroup G} (hL : L ∈ cComp X) (hS : SporadicSix (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ¬ A38Types ↥((L.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) := fun hA =>
  kN G L hS ((a38Types_image_iff hL).mp hA)

theorem g1_le_normalizer_of_sporadic (h38 : A38ForSQTK) (kN : SporadicSixNotA38) {G : Type}
    [Group G] [Finite G] {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hcomp : IsComponentOf L (g1_1516 Z₁))
    (hS : SporadicSix (↥L ⧸ CFSG.pCore 2 ↥L)) : g1_1516 Z₁ ≤ Subgroup.normalizer (L : Set G) := by
  have hLcomp : L ∈ cComp (g1_1516 Z₁) :=
    Id2519.mem_cComp_of_isComponentIn (DoubleA3.isComponentIn_iff_open.mpr hcomp)
  have hsqtk : IsSQTKIn (g1_1516 Z₁) := hc.h18.five.2.2.sqtk
  exact GoldMLB.normalizes_of_not_a38 h38 hsqtk hLcomp (not_a38Types_image_of_sporadic kN hLcomp hS)

end CFSG.Quasithin.S151S9U

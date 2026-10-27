module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinGenMember
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

namespace NSJoin

section Def


@[expose] def NSWeakNonUnitaryInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      NSJoinGuardOf T p L Bs 𝒦 →
      ∀ K : Subgroup G, GGSecFiveWeakNbr p B Bs x L D J 𝒦 K → ¬ GGSplitLie p K →
        ¬ GGMemberUnitary p Bs K →
          (∀ r ∈ ggAutomizer K Bs, GGIsReflection p r → GGRk1Concl p Bs K r) ∧
          K ≤ ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer K Bs), ⨆ (_ : GGIsReflection p r),
            ggRankOneIn K Bs r

end Def

end NSJoin

end CFSG.StandardType

end

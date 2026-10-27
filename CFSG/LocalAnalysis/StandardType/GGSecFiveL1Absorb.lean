module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1AbsorbAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Quasithin

theorem ggRankOnePerf_le_rankOneIn_of_subnormal {G : Type} [Group G] [Finite G]
    {Bs X Z : Subgroup G} {r : MulAut ↥Bs}
    (hXS : IsSubnormal X Z)
    (hMZ : Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤ Z)
    (hQ : CFSG.Assembly.IsQuasisimple ↥(ggRankOnePerf Bs r))
    {n u : G} (hn : n ∈ X ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G))
    (hu : u ∈ ggRankOnePerf Bs r) (hnu : n * u ≠ u * n) :
    ggRankOnePerf Bs r ≤ ggRankOneIn X Bs r := by
  let M : Subgroup G := Subgroup.centralizer (ggHyperplane Bs r : Set G)
  have hMZ' : M ≤ Z := hMZ
  have hT : IsSubnormal (X ⊓ M) M := ggL1Ab_inf_isSubnormal hXS hMZ'
  have hPM : ggRankOnePerf Bs r ≤ M := perfectCore_le M
  have hcomp : IsComponentOf (ggRankOnePerf Bs r) M :=
    ⟨hPM, ggIsSubnormal_of_normal hPM (perfectCore_normal M), hQ⟩
  rcases isComponentOf_le_or_commutator_eq_bot hcomp hT with hle | hcomm
  · exact ggL1Ab_perfect_le_ggOTwoPrime_of_le hle (perfectCore_perfect M)
  · exact absurd hcomm (ggL1Ab_commutator_ne_bot_of_not_commute hu hn hnu)

end CFSG.StandardType

end

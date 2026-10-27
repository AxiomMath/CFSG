module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.Quasithin.Background.A3Structure38Facts
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Quasithin

theorem ggRankOnePerf_eq_of_solvable_pieces {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} {r : MulAut ↥Bs}
    (hperf : ⁅ggRankOneIn X Bs r, ggRankOneIn X Bs r⁆ = ggRankOneIn X Bs r)
    (hpi : ggRankOnePerf Bs r ≤ ggRankOneIn X Bs r ⊔ Subgroup.centralizer (X : Set G))
    (hsolv : Group.IsSolvable ↥(Subgroup.centralizer (X : Set G) ⊓
      Subgroup.centralizer (ggHyperplane Bs r : Set G))) :
    ggRankOnePerf Bs r = ggRankOneIn X Bs r := by
  have hS_inf : ggRankOneIn X Bs r ≤
      X ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G) :=
    ggOTwoPrime_le _
  have hSX : ggRankOneIn X Bs r ≤ X := hS_inf.trans inf_le_left
  have hSC : ggRankOneIn X Bs r ≤ Subgroup.centralizer (ggHyperplane Bs r : Set G) :=
    hS_inf.trans inf_le_right
  have hSP : ggRankOneIn X Bs r ≤ ggRankOnePerf Bs r :=
    le_perfectCore_of_perfect hSC hperf
  have hPC : ggRankOnePerf Bs r ≤ Subgroup.centralizer (ggHyperplane Bs r : Set G) :=
    perfectCore_le _
  have hZS : Subgroup.centralizer (X : Set G) ≤
      Subgroup.centralizer (ggRankOneIn X Bs r : Set G) :=
    Subgroup.centralizer_le hSX
  have hZNS : Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer (ggRankOneIn X Bs r : Set G) :=
    hZS.trans (Subgroup.centralizer_le_normalizer _)
  have hSNZ : ggRankOneIn X Bs r ≤
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) :=
    ((Subgroup.le_centralizer_iff).mpr hZS).trans (Subgroup.centralizer_le_normalizer _)
  have hdedekind : ggRankOnePerf Bs r =
      ggRankOneIn X Bs r ⊔
        (ggRankOnePerf Bs r ⊓ Subgroup.centralizer (X : Set G)) :=
    CFSG.Quasithin.A3.eq_sup_inf_of_le_sup
      (L := ggRankOneIn X Bs r) (N := Subgroup.centralizer (X : Set G))
      (P := ggRankOnePerf Bs r) hSNZ hSP hpi
  have hPZ : ggRankOnePerf Bs r ⊓ Subgroup.centralizer (X : Set G) ≤
      Subgroup.centralizer (X : Set G) ⊓
        Subgroup.centralizer (ggHyperplane Bs r : Set G) :=
    le_inf inf_le_right (inf_le_left.trans hPC)
  have hPY : ggRankOnePerf Bs r ≤ ggRankOneIn X Bs r ⊔
      (Subgroup.centralizer (X : Set G) ⊓
        Subgroup.centralizer (ggHyperplane Bs r : Set G)) :=
    (le_of_eq hdedekind).trans (sup_le_sup_left hPZ (ggRankOneIn X Bs r))
  have hYsolv : Group.IsSolvable ↥(Subgroup.centralizer (X : Set G) ⊓
      Subgroup.centralizer (ggHyperplane Bs r : Set G)) := hsolv
  have hYNS : (Subgroup.centralizer (X : Set G) ⊓
      Subgroup.centralizer (ggHyperplane Bs r : Set G)) ≤
        Subgroup.normalizer (ggRankOneIn X Bs r : Set G) :=
    inf_le_left.trans hZNS
  have hAnorm : ((ggRankOneIn X Bs r).subgroupOf
      (ggRankOneIn X Bs r ⊔ (Subgroup.centralizer (X : Set G) ⊓
        Subgroup.centralizer (ggHyperplane Bs r : Set G)))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hYNS)
  have hcore : perfectCore (ggRankOneIn X Bs r ⊔
      (Subgroup.centralizer (X : Set G) ⊓
        Subgroup.centralizer (ggHyperplane Bs r : Set G))) ≤ ggRankOneIn X Bs r :=
    perfectCore_le_of_sup_solvable (A := ggRankOneIn X Bs r)
      (B := Subgroup.centralizer (X : Set G) ⊓
        Subgroup.centralizer (ggHyperplane Bs r : Set G))
      (Y := ggRankOneIn X Bs r ⊔
        (Subgroup.centralizer (X : Set G) ⊓
          Subgroup.centralizer (ggHyperplane Bs r : Set G)))
      le_sup_left hAnorm rfl hYsolv
  have hPP : ⁅ggRankOnePerf Bs r, ggRankOnePerf Bs r⁆ = ggRankOnePerf Bs r :=
    perfectCore_perfect _
  have hPS : ggRankOnePerf Bs r ≤ ggRankOneIn X Bs r :=
    (le_perfectCore_of_perfect hPY hPP).trans hcore
  exact le_antisymm hPS hSP

theorem ggRankOnePerf_eq_iff_rankOneIn_perfect {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} {r : MulAut ↥Bs}
    (hPS : ggRankOnePerf Bs r ≤ ggRankOneIn X Bs r) :
    ggRankOnePerf Bs r = ggRankOneIn X Bs r ↔
      ⁅ggRankOneIn X Bs r, ggRankOneIn X Bs r⁆ = ggRankOneIn X Bs r := by
  constructor
  · intro hEq
    rw [← hEq]
    exact perfectCore_perfect _
  · intro hperf
    have hSC : ggRankOneIn X Bs r ≤
        Subgroup.centralizer (ggHyperplane Bs r : Set G) :=
      (ggOTwoPrime_le _).trans inf_le_right
    have hSP : ggRankOneIn X Bs r ≤ ggRankOnePerf Bs r :=
      le_perfectCore_of_perfect hSC hperf
    exact le_antisymm hPS hSP

end CFSG.StandardType

end

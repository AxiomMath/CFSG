module

public import CFSG.Literature.Janko67
public import CFSG.RankThree.GF2n.Parrott.A1TheoremA
public import CFSG.RankThree.GF2n.Parrott.ParrottFi22CitedS
public import CFSG.RankThree.GF2n.Parrott.Section2Theorem1EqualityBranchHolds
public import CFSG.RankThree.GF2n.Parrott.Section5Theorem5Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFInduces
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFKindDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Layer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Defs

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup

theorem parrott_theorem5_holds :
    ∀ (G : Type) [Group G] [Finite G] (z : G), Tim79a.ParrottHyp z →
      centerIn (inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G))) ≠
        centerIn (Subgroup.centralizer ({z} : Set G)) →
      Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤ →
        CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22 :=
  parrott_theorem5_export (parrott_theoremA_one_cited CFSG.Literature.Janko67.janko_psp43)
    parrott_theorem1_equalityBranch_holds

end CFSG.RankThree.GF2n.Parrott

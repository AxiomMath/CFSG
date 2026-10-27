module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSzPointAction
public import CFSG.CGT.PushingUpLit.BHS7.OmegaSL
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzAutRank
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieG
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22r3e5c_isSylowTwoOf_barImage_inf_T {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) :
    IsSylowTwoOf (barImage L (D.T ⊓ L)) ⊤ := by
  have hTL : IsSylowTwoOf (D.T ⊓ L) L :=
    CFSG.CGT.PushingUpLit.BHS7.isSylowTwoOf_inf_of_isSubnormal hL.1
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr D.sylowM)
  exact CFSG.Quasithin.H13.S126P31.isSylowTwoOf_map_mk' (Z := CFSG.pCore 2 ↥L)
    (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hTL)

theorem uc22r3e5c_card_barImage_inf_T {D : Data G}
    {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hSz : IsSz (Bar2 L) n) :
    Nat.card ↥(barImage L (D.T ⊓ L)) = (2 ^ n) ^ 2 := by
  have h := uc22r3e5c_isSylowTwoOf_barImage_inf_T hL
  let Q : Sylow 2 (Bar2 L) := h.2.1.toSylow (by
    rw [← Subgroup.relIndex_top_right (H := barImage L (D.T ⊓ L))]; exact h.2.2)
  have hQ : (Q : Subgroup (Bar2 L)) = barImage L (D.T ⊓ L) := IsPGroup.toSylow_coe _ _
  rw [← hQ]
  let T := szPointActionFacts_holds (Bar2 L) n hSz
  exact T.card_sylow Q


end CFSG.LocalAnalysis.UniquenessCase.UC22

end

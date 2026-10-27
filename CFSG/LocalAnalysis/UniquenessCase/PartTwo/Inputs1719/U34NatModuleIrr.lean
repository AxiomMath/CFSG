module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3NatModuleIrr
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Setup

theorem u34NatModule_of_irr
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hSU : IsSU3 ↥L 2)
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hm : E3.mParam Y < 2 * 2 + 2) :
    NatSUn L ⊤ ⊥ 3 2 ∧ E3.mParam Y = 2 * 2 :=
  su3NatModule_of_irr hW hLY hLn (le_refl 2) hSU hirr (by omega)

theorem u34NatModule_of_rankThreeIrr
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hSU : IsSU3 ↥L 2) (hirr : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn L)
    (hm : E3.mParam Y ≤ 2 * 2) :
    NatSUn L ⊤ ⊥ 3 2 ∧ E3.mParam Y = 2 * 2 :=
  u34NatModule_of_irr hW hLY hLn hSU hirr (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

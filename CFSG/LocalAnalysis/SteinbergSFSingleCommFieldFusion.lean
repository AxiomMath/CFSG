module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionCard
public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionCoset
public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionSeries
public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionFixed
public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionExclude

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

theorem field_fusion
    (hSel : CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootSelector fun D _ => CFSG.Blueprint.Catalog D) :
    FieldFusionStatement := by
  intro G _ _ _ L K _ _ _ n φ t i hS hH hE hK
  have f0 := sixFF_ff0 hK
  have f1 := sixFF_ff1 hS hH hK
  have f2 := sixFF_ff2 hS
  have f3a := sixFF_ff3a hS hH
  have f3 := sixFF_ff3 hS hH hK f0 f1 f2 f3a
  have f5 := sixFF_ff5 hS f2
  have f6 := sixFF_ff6 hS hH hK f1 f2 f3
  have f7 := sixFF_ff7 hSel hS hH
  have f8 := sixFF_ff8 hS hH hE hK f7
  have f9 := sixFF_ff9 hS hH hE hK f5 f6 f7 f8
  exact ⟨f3, fun g hg => hK.slice g (f9 g hg)⟩

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard

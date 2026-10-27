module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3Bridge
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3Use
public import CFSG.LocalAnalysis.SteinbergSFSingleCommEmbeddedNormal
public import CFSG.LocalAnalysis.SteinbergSFSingleCommEmbeddedFactor

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

theorem six_Emb
    (hSel : CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootSelector fun D _ => CFSG.Blueprint.Catalog D) :
    EmbStatement := by
  intro G _ _ _ L K _ _ _ n φ t i hS hH
  have he1 := sixEmb_e1 hS
  have he2 := sixEmb_e2_of_model3 hS hH he1 (sc_model3_sub hSel hS)
  have he5 := sixEmb_e5 hS hH
  exact ⟨sixEmb_e3 hS hH he2, sixEmb_e4 hS, he5, sixEmb_e6 hS hH he5⟩

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard

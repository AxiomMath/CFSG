module

public import CFSG.Sporadic.Schreier.J4SOutOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic

public section

namespace CFSG.ComponentClassification.CatalogueU

theorem sporadicOddCoreFree_J4 :
    SporadicOddCoreFree .J4 :=
  fun _ _ _ hF hnab ⟨e⟩ t ht =>
    Sporadic.J4Schreier.CTU_J4_full_group_involution_odd_core hF hnab
      (e.trans (Sporadic.J4.seedEquiv Sporadic.J4.j4Facts.mat)) t ht

end CFSG.ComponentClassification.CatalogueU

namespace CFSG.Sporadic.J4Schreier

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint CFSG.Sporadic.J4

theorem outer_carrier_J4_odd :
    Odd (Nat.card (Outer (NativeSporadic.Carrier .J4))) := by
  rw [@card_outer_congr (NativeSporadic.Carrier .J4) J (NativeSporadic.carrierGroup .J4)
    (Subgroup.toGroup J) (seedEquiv j4Facts.mat)]
  exact CTU_J4_outer_automorphism_group_odd_order

end CFSG.Sporadic.J4Schreier

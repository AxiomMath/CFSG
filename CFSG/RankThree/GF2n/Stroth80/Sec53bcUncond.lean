module

public import CFSG.RankThree.GF2n.Stroth80.Sec53cFixPair
public import CFSG.RankThree.GF2n.Stroth80.Sec53Odd

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Certs

theorem vone_neStatement_holds (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ≠ Vt M (LB M Q B) B Z t :=
  vone_ne_of_odd h34 hRoot h51 (stroth53Odd_holds h34 hRoot h51)
    (fun G _ _ M Q Z B hc n t hs hsp r hr hplane _ =>
      stroth53FixB_holds h34 hRoot h51 G M Q Z B hc n t hs hsp r hr hplane)
    (fun G _ _ M Q Z B hc n t hs hsp r hr hplane _ =>
      stroth53FixC_holds h34 hRoot h51 G M Q Z B hc n t hs hsp r hr hplane)

theorem stroth53bStatement_holds (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) : Stroth53bStatement :=
  stroth53b_of_51_prod h51 (stroth53bProd_of_vone_ne h34 hRoot h51
    (vone_neStatement_holds h34 hRoot h51))

theorem stroth53cStatement_holds (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) : Stroth53cStatement :=
  stroth53c_of_53b_components (stroth53bStatement_holds h34 hRoot h51)
    (stroth53VW_holds h34 hRoot h51) (stroth53Inf_holds)
    (stroth53FixB_holds h34 hRoot h51) (stroth53FixC_holds h34 hRoot h51)

end Certs

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.RankThree.GF2n.Stroth80.Sec54Vone
public import CFSG.RankThree.GF2n.Stroth80.Sec53Odd
public import CFSG.RankThree.GF2n.Stroth80.Sec53cFixPair

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Certs

theorem stroth53aStatement_holds (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) : Stroth53aStatement := by
  have hOdd := stroth53Odd_holds h34 hRoot h51
  have hne := vone_ne_of_odd h34 hRoot h51 hOdd
    (fun G _ _ M Q Z B hc n t hs hsp r hr hplane _ =>
      stroth53FixB_holds h34 hRoot h51 G M Q Z B hc n t hs hsp r hr hplane)
    (fun G _ _ M Q Z B hc n t hs hsp r hr hplane _ =>
      stroth53FixC_holds h34 hRoot h51 G M Q Z B hc n t hs hsp r hr hplane)
  exact stroth53a_of_vone_ne h34 hRoot h51 hne hOdd

theorem sec54_vone_eq_Wt (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n m : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hm : 2 ≤ m) (hV : SpMNat hc t m)
    (hN : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z)
    {r : G} (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    Sec8V1 M Q Z B t r = Sec8W1 M Q Z B t r :=
  sec54_vone_eq_Wt_of_53a h34 hRoot h51 (stroth53aStatement_holds h34 hRoot h51)
    hc hs hm hV hN hr hplane

end Certs

end CFSG.RankThree.GF2n.Stroth80

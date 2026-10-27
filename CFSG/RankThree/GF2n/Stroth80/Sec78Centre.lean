module

public import CFSG.RankThree.GF2n.Stroth80.Sec78CommW
public import CFSG.RankThree.GF2n.Stroth80.Sec78Z1
public import CFSG.RankThree.GF2n.Stroth80.Sec78VtIrred
public import CFSG.RankThree.GF2n.Stroth80.Sec78Z0Data

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem sec7ZCard_of_inputs (h51 : Stroth51Statement) (hA : Sec7AExistsStatement) :
    Sec7ZCardStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  exact sec7ctr_card_Z0 h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0
    (sec7ctr_Z0_le_CN hc hs hZ0)

theorem sec7CentreMp_of_inputs (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) : Sec7CentreMpStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 x hx
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hZN := sec7ctr_Z0_le_CN hc hs hZ0
  have hnat : SpNat hc t ∨ OmegaNat hc t := Or.inr hs.omegaNat
  have hZB := sec7ctr_Z0_le_LB h51 hc hs.toSec5 hnat hr hZ0 hZN
  have hZC := sec7ctr_Z0_le_LC h51 hc hs.toSec5 hnat hr hZ0 hZN
  exact ⟨hZB hx, sec7ctr_comm_W_le_Z h52a sec7VtIrred_holds hc hs hr hZ0 hZN hZB hZC hx⟩

end CFSG.RankThree.GF2n.Stroth80

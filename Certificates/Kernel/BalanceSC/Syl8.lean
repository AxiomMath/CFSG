module

public import Certificates.Kernel.BalanceSC.Data
public import Certificates.Kernel.BalanceSC.SylData
public import Certificates.Data.Kernel.BalanceSC.Sylow

public section

namespace CFSG.KD.BalSC8

open CFSG.KC.BalanceSC CFSG.KC.Misc.ArrEnum

theorem tabHead :
    headK (nat_lit 8) (nat_lit 4) (nat_lit 3) (nat_lit 64) (getL (nat_lit 0) G) (tab64 PB) =
      true := by
  decide +kernel

theorem tabPoints :
    pointsK (nat_lit 8) (nat_lit 4) (nat_lit 3) (nat_lit 64) (getL (nat_lit 0) G) (tab64 PB)
      (fun i k => getL (nat_lit 0) (getL [] E i) k) (getL (nat_lit 0) PAR) (getL (nat_lit 0) LAB)
      (nat_lit 0) (nat_lit 64) = true := by
  decide +kernel

theorem tabKeys : keysK (nat_lit 8) (nat_lit 4) PS (tab64 PB) (nat_lit 0) (nat_lit 64) = true := by
  decide +kernel

theorem isoI : eqL I (isoIdxK (nat_lit 8) (nat_lit 64) (tab64 PB)) = true := by decide +kernel

theorem nbr : nbrK (nat_lit 8) (tab64 PB) I = true := by decide +kernel

theorem conn : connK (nat_lit 8) (tab64 PB) I ORD = true := by decide +kernel

theorem rank : rankK (nat_lit 8) (tab64 PB) I = true := by decide +kernel

theorem eight : eightK (nat_lit 8) (tab64 PB) I = true := by decide +kernel

theorem half : halfK (nat_lit 8) (nat_lit 64) (tab64 PB) I = true := by decide +kernel

end CFSG.KD.BalSC8

end

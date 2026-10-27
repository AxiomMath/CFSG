module

public import Certificates.Kernel.AutJ2Lat.Defs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.AutJ2Lat

open CFSG.KC.IdxG

theorem x_ok : xOK = true := by quickRfl

theorem ab_ok : abOK = true := by quickRfl

theorem s_ok : sOK = true := by quickRfl

theorem wa_ok : waOK = true := by quickRfl

theorem c_ok : cOK = true := by quickRfl

theorem conj_ok : conjOK = true := by quickRfl

theorem mc_ok : mcOK = true := by quickRfl

theorem mw_ok : mwOK = true := by quickRfl

theorem oms : (List.range 5).all omOK = true := by quickRfl

theorem om_sizes : (((List.range 5).map fun j => (Om j).lbl.size) == [1, 9, 15, 3, 3]) = true := by
  quickRfl

theorem ots : (List.range 5).all otOK = true := by quickRfl

theorem mw_lt2 : (AutJ2Lat.RL.mw.all fun ws => ws.all fun w => w.all (Nat.blt · 2)) = true := by
  quickRfl

theorem gens31 : gensB 3 1 = true := by quickRfl

theorem gens41 : gensB 4 1 = true := by quickRfl

theorem gens42 : gensB 4 2 = true := by quickRfl

theorem fix_ok : fixB = true := by quickRfl

theorem move_ok : moveB = true := by quickRfl

theorem top_ok : topB = true := by quickRfl

theorem codes_ok : codesBelow 315 Δc = true := by quickRfl

end CFSG.KD.AutJ2Lat

end

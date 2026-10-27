module

public import CFSG.Sporadic.Schreier.M11Data
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8M11DataInputs
import Certificates.Kernel.LocalQT.M11.C4154
import CFSG.Certificates.Kernel.LocalQTM11GrpProved
import CFSG.Sporadic.Schreier.M11

public section

namespace Certificates

open CFSG.KD.LQT.C4154 CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Unc25M11 in
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu in
theorem certificate4154 : (m11Elements.all (fun g => decide (NormProp g)) = true)
    ∧ (m11Elements.all centB = true) := by
  have h := CFSG.KC.LQT.M.s4154_proved m11gA m11gB _ _ _ m11Elements
    (fun g => by rw [mem_m11Elements, m11_eq]) CFSG.KD.LQT.M11.ha CFSG.KD.LQT.M11.hb hsa hsb hp CFSG.KD.LQT.M11.hg hk
  exact ⟨List.all_eq_true.2 fun g hg => decide_eq_true (h.1 g hg),
    List.all_eq_true.2 fun g hg => List.all_eq_true.2 fun t ht => List.all_eq_true.2 fun s hs =>
      decide_eq_true (h.2 g hg t ht s hs)⟩

end Certificates

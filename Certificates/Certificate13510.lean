module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_8Inputs
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Kernel.PermCent.K13510
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.L34T

namespace Certificates

private theorem l34Seven_eq : CFSG.HardMathSupport.Solomon.Coordinator.l34SevenCheck () = sevenC := by
  have h7 := fun g : CV 42 => orderIs_eq_orderIsP g (m := 7) (by norm_num) [7]
    (fun p hp hd => by simp [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hd])
    (by decide)
  unfold CFSG.HardMathSupport.Solomon.Coordinator.l34SevenCheck sevenC
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC]
  simp only [List.all_map, List.any_map, List.filter_map, Function.comp_def, ev_mul', ev_inv',
    one_eq_ev, ne_eq, ev_eq_iff, sift_ev, orderIs_ev, h7]

theorem certificate13510 : CFSG.HardMathSupport.Solomon.Coordinator.l34SevenCheck () = true := by
  rw [l34Seven_eq, sevenC_eq_sevenQ, ← sevenH_eq]
  exact k13510

end Certificates

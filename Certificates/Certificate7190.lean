module

public import Certificates.Data.SmithB45MatHat
import Certificates.Kernel.HMathieu.T12GlueF
import Certificates.Kernel.HMathieu.C7190
import CFSG.Certificates.Kernel.HMathieu.FixTabSound
import CFSG.Certificates.Kernel.HMathieu.PredSound

public section

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12 CFSG.Quasithin.B45Mat
open CFSG.KC.HMathieu CFSG.QuasithinUnique.Setup.X1 CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12 CFSG.Quasithin.B45Mat in
theorem certificate7190 :
    ∀ [Fact (T12s2.check = true)],
      forallGreedyAll pos12s2F inv12s2F (predR 10 act12s2) 3 [] = true := by
  intro _
  have hMc : T12.Mc.length = 36 := by rw [T12.mcOK, List.length_map, T12.lenPF]
  have hFs : ∀ y < inv12s2F.length,
      FixTab12.F12.getD y [] = fixMasks 10 actM [T12.Mc.getD y []] := by
    intro y hy
    rw [T12.lenF] at hy
    rw [fixTab_get FixTab12.tab y (by simp [hMc]; omega)]
    simp [fixMasks, List.getD_eq_getElem?_getD, List.getElem?_take, hy]
  refine forallGreedyAll_fixT T12.gtabsF (by rw [T12.lenF]; exact T12.lenOK.2)
    (fun x => T12s2.posArr_spec _ x) T12.Mc FixTab12.F12 10 hFs (predR 10 act12s2) (predRK 10)
    (fun l hl _ => ?_) 3 (by rw [T12.lenF]; exact C7190.search)
  unfold predR predRK fixSt
  rw [fixMasks_map 10 (fun x => T12.Mc.getD (inv12s2F.idxOf x) [])
    (fun x hx => T12.act_memF (hl x hx)), List.length_map, List.isEmpty_map]

end Certificates

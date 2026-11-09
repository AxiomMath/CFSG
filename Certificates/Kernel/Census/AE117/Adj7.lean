module

public import Certificates.Data.Kernel.AE117Adj
import CFSG.Certificates.Kernel.AE117AdjSound

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

open Certificates.Kernel.AE117Adj

theorem adj7_all_split {α : Type} (l : List α) (k : Nat) (f : α → Bool) :
    l.all f = ((l.take k).all f && (l.drop k).all f) := by
  conv_lhs => rw [← List.take_append_drop k l]
  rw [List.all_append]

theorem adj7_d : (quads 7).all dOK = true := by decide +kernel

theorem adj7_p0 :
    ((quads 7).take 12).all (fun q => (quads 7).all fun q' => adjPairW q q') = true := by
  decide +kernel

theorem adj7_p1 :
    (((quads 7).drop 12).take 12).all (fun q => (quads 7).all fun q' => adjPairW q q') = true := by
  decide +kernel

theorem adj7_p2 :
    (((quads 7).drop 12).drop 12).all (fun q => (quads 7).all fun q' => adjPairW q q') = true := by
  decide +kernel

theorem adjCheckLW_seven : Certificates.Kernel.AE117Adj.adjCheckLW 7 = true := by
  unfold adjCheckLW
  rw [adj7_d, adj7_all_split (quads 7) 12 (fun q => (quads 7).all fun q' => adjPairW q q'), adj7_p0,
    adj7_all_split ((quads 7).drop 12) 12 (fun q => (quads 7).all fun q' => adjPairW q q'), adj7_p1,
    adj7_p2]
  all_goals rfl

theorem adjCheckL_seven : Certificates.Kernel.AE117Adj.adjCheckL 7 = true :=
  Certificates.Kernel.AE117Adj.adjCheckL_of_W adjCheckLW_seven

end CertificateChecks.KernelCensus

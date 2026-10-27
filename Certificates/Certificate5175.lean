module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeA7Inputs
import Certificates.Kernel.A7Ai.Checks
import CFSG.Certificates.Kernel.PermCent.A7AiCSound

public section

open CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree.A7Ai CFSG.Certificates.Kernel.PkCV
  Certificates.Kernel.A7Ai

namespace Certificates

open CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree.A7Ai in
theorem certificate5175 : a7aiCheck = true := by
  simp only [a7aiCheck, Bool.and_eq_true, decide_eq_true_eq, tab_eq]
  exact ⟨a7aiA_of a7aiAF_true, a7aiB_of a7aiBF_true⟩

end Certificates

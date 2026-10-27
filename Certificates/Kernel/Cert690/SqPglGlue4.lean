module

public import Certificates.Kernel.Cert690.SqPglGlue
public import Certificates.Kernel.Cert690.SqPglCnt
public import CFSG.Certificates.Kernel.Cert690.SqPglS4Sound

public section

namespace CertificateChecks.KernelC690.SqPgl

open CFSG.KC.C690 CFSG.GF2Type.Smith1979W3.Cert690 CertificateChecks.KernelC690.Pgl

theorem outOKP : pglOutersOK (pglData ()) = true := by
  have e := pglFactsP
  unfold pglFactsCheck at e
  simp only [Bool.and_eq_true] at e
  have e12 := e.1.2
  unfold pglF12Of at e12
  simp only [Bool.and_eq_true] at e12
  exact e12.1.1.1.2

theorem pglS4P : pglS4Of (pglSquareData ()) = true :=
  pglHyp.s4 outOKP selX i0X cmX frX recX csX bodyX rootV.2

theorem pglSquareP : pglSquareCheck () = true := by
  unfold pglSquareCheck
  dsimp only
  rw [pglS1P, pglS2P, pglS3P, pglS4P]
  rfl

end CertificateChecks.KernelC690.SqPgl

end

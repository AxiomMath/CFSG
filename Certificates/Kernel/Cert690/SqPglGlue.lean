module

public import Certificates.Kernel.Cert690.SqPglChk
public import Certificates.Kernel.Cert690.PglGlue
public import CFSG.Certificates.Kernel.Cert690.SqPglSound

public section

namespace CertificateChecks.KernelC690.SqPgl

open CFSG.KC.C690 CFSG.GF2Type.Smith1979W3.Cert690 CertificateChecks.KernelC690.Pgl

theorem invOKP : pglInvolutionsOK (pglData ()) = true := by
  have e := pglFactsP
  unfold pglFactsCheck at e
  simp only [Bool.and_eq_true] at e
  have e12 := e.1.2
  unfold pglF12Of at e12
  simp only [Bool.and_eq_true] at e12
  exact e12.1.1.1.1

theorem pglHyp : PglHyp K K0 par par0 (idxT S) (idxT W1) (idxT W2) M1 M2 where
  enum := enumK_eq
  enum0 := enumK0_eq
  invOK := invOKP
  nd := ix.1
  ix := ix.2
  iso := isoQ_of_enumPar (by rw [lenK]; norm_num) (by rw [← List.head?_eq_getElem?]; exact headK)
    (by rw [oneF_eq]; exact isoGens.2) enumK.1 isoGens.1
  inv := invK
  pass1 := by rw [← r12.1]; exact pass1
  pass2 := by rw [← r12.2]; exact pass2
  bits := bitsK
  top := by rw [lenK]; exact bitsTop
  memR := memR
  inv1 := invR.1
  inv2 := invR.2
  root1 := root1
  root2 := root2

theorem pglS1P : pglS1Of (pglSquareData ()) = true := pglHyp.s1

theorem pglS2P : pglS2Of (pglSquareData ()) = true := pglHyp.s2

theorem pglS3P : pglS3Of (pglSquareData ()) = true := pglHyp.s3

end CertificateChecks.KernelC690.SqPgl

end

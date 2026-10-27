module

public import Certificates.Kernel.Cert690.SqA8Chk
public import Certificates.Kernel.Cert690.SqA8Root
public import Certificates.Kernel.Cert690.SqPassChk
public import Certificates.Kernel.Cert690.GlueP
public import CFSG.Certificates.Kernel.Cert690.SqA8Sound

public section

namespace CertificateChecks.KernelC690.SqPass

open CFSG.KC.C690 CFSG.GF2Type.Smith1979W3.Cert690 CertificateChecks.KernelC690.GrpP

theorem a8Gens_eq : a8Gens = omegaGensC false := by rw [omGens]; rfl

theorem a8Hyp : A8Hyp Om omPar (idxT Sm) (idxT W1) (idxT W2) M1 M2 r1 r2 where
  enum := by rw [a8Gens_eq]; exact checks.enumOm
  nd := checks.ixm.1
  ix := checks.ixm.2
  len := lenOm
  eok := enumOK_of ixOm checks.len_le_m checks.headm parOm clOm invGOm
  iso := isoQ_of_enumPar checks.len_le_m om012.1 (by rw [oneF_eq]; exact isoGens.2) parOm
    isoGens.1
  gens := isoGens.1
  isoOne := isoGens.2
  inv := invOm
  pass1 := pass1
  pass2 := pass2
  bits := bitsOm
  top := by rw [lenOm]; exact bitsTop
  l0 := om012.1
  l1 := om012.2.1
  l2 := om012.2.2
  inv1 := by rw [r12.1]; exact invR.1
  inv2 := by rw [r12.2]; exact invR.2.1
  one := invR.2.2
  m11 := m1Bits.1
  m12 := m1Bits.2
  root1 := by rw [r12.1]; exact root1
  root2 := by rw [r12.2]; exact root2

theorem a8S1P : a8S1Of (a8Data ()) = true := a8Hyp.s1

theorem a8S2P : a8S2Of (a8Data ()) = true := a8Hyp.s2

theorem a8S3P : a8S3Of (a8Data ()) = true := a8Hyp.s3

theorem a8S4P : a8S4Of (a8Data ()) = true := a8Hyp.s4

end CertificateChecks.KernelC690.SqPass

end

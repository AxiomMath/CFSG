module

public import Certificates.Data.CommProdM23
public meta import Certificates.Data.CommProdM23
import Certificates.Kernel.SporSch.Mathieu.M23Comm

public section

namespace Certificates

open CertificateChecks

theorem certificate5155 : CommProd.commProdOK CFSG.OddStandard.m23Cg1 CommProd.m23CentPerfWit = true :=
  KernelSporSch.M23Comm.commProd

end Certificates


module

public import Certificates.Certificate5122Base

public import CFSG.GH74.KGroups.L34Inputs
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.PermCent.K5138
import Certificates.Kernel.PermCent.KG5122
import Certificates.Data.Kernel.PermCent.KGrpC

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp CFSG.Certificates.Kernel.PkEnum

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.L34 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix in
theorem certificate5122 : (QP21.check = true ∧ QP21.orderCertificate = 20160)
    ∧ (QP.check = true ∧ QP.orderCertificate = 20160)
    ∧ (blockHom 21 21 (pa, pa') = PA ∧ blockHom 21 21 (pb, pb') = PB) :=
  ⟨⟨check_certificate_of _ _ _ _ _ K5122.kQP21.1,
    (orderCertificate_eq_orderV _).trans K5122.kQP21.2⟩,
    ⟨check_certificate_of _ _ _ _ _ L34MT.kQP, (orderCertificate_eq_orderV _).trans K5122.kQP⟩,
    K5122.kBlk⟩

end Certificates

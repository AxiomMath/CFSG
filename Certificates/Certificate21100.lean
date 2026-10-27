module

public import Certificates.Kernel.Co2Census.CCSyl
public import Certificates.Kernel.Co2Census.CCX1
public import Certificates.Kernel.Co2Census.CCClass

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelCo2Census

theorem certificate21100 :     CFSG.Sporadic.Co2Smith.CCFacts := by
  intros
  exact
    { classes := cc_classes.1
      cls := cc_classes.2
      sqrt := cc_sqrt
      ce := fun i => (cc_rep i).2.2.2.1
      invE := fun i => (cc_rep i).2.2.2.2
      c3 := cc_c3
      c2B_comm := c7_comm
      c2B_cxd := c7_cxd
      c2B_zd := c7_zd
      c2B_za := c7_za
      c2B_hmin := c7_hmin
      c1_comm := KernelCo2Census.c1_comm
      c1_hmin := KernelCo2Census.c1_hmin
      c1_cxd_card := KernelCo2Census.c1_cxd_card
      c1_cxd_sq := KernelCo2Census.c1_cxd_sq
      c1_j := KernelCo2Census.c1_j
      c1_two := KernelCo2Census.c1_two
      syl := cc_syl }

end Certificates

module

public import Certificates.Data.Asc1113M22
meta import Certificates.Data.Asc1113M22

public section

namespace Certificates

open CFSG.M23 CFSG.Mathieu.Asc1113M22

set_option maxRecDepth 10000 in
theorem certificate660109_usq : u * u = 1 := by decide +kernel
set_option maxRecDepth 10000 in
theorem certificate660109_uau : evalGroupWord S2 wordUAU = u * S2 0 * u⁻¹ := by decide +kernel
set_option maxRecDepth 10000 in
theorem certificate660109_ubu : evalGroupWord S2 wordUBU = u * S2 1 * u⁻¹ := by decide +kernel

theorem certificate660109 :
    CFSG.Mathieu.Asc1113M22.u * CFSG.Mathieu.Asc1113M22.u = 1 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S2
          CFSG.Mathieu.Asc1113M22.wordUAU =
        CFSG.Mathieu.Asc1113M22.u * CFSG.Mathieu.Asc1113M22.S2 0 *
          CFSG.Mathieu.Asc1113M22.u⁻¹ ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S2
          CFSG.Mathieu.Asc1113M22.wordUBU =
        CFSG.Mathieu.Asc1113M22.u * CFSG.Mathieu.Asc1113M22.S2 1 *
          CFSG.Mathieu.Asc1113M22.u⁻¹ :=
  ⟨certificate660109_usq, certificate660109_uau, certificate660109_ubu⟩

end Certificates

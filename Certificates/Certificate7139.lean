module

public import Certificates.Data.H9FourJ
import Certificates.Kernel.H9Four.J7139
import CFSG.Certificates.Kernel.H9Four.JGlue

public section

open CFSG.KC.H9Four.JGlue CFSG.KD.H9Four.J

namespace Certificates

open CFSG.Quasithin.H13.H9Four in
theorem certificate7139 : s0Check = true ∧ j0Check = true ∧ x0Check = true ∧ oddGenCheck = true ∧
    lineCheck = true ∧ fixCheck = true ∧ kerCheck = true ∧ e9Check = true ∧ ffRepCheck = true ∧
    u0Check = true :=
  ⟨s0Check_of ch7139_canon ch7139_s0, j0Check_of ch7139_canon ch7139_j0,
    x0Check_of ch7139_canon ch7139_x0, oddGenCheck_of ch7139_canon ch7139_odd,
    lineCheck_of ch7139_canon ch7139_line, fixCheck_of ch7139_canon ch7139_fix,
    kerCheck_of ch7139_canon ch7139_ker, e9Check_of ch7139_canon ch7139_e9,
    ffRepCheck_of ch7139_canon ch7139_ff, u0Check_of ch7139_canon ch7139_u0⟩

end Certificates

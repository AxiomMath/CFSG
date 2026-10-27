module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.W4RowLane.LyGlue

public section

namespace Certificates

theorem certificate1037001 : ∀ t : CFSG.Blueprint.NativeSporadic.Ly, t * t = 1 → t ≠ 1 →
    ∃ c : CFSG.Blueprint.NativeSporadic.Ly, orderOf (t * (c * t * c⁻¹)) = 67 :=
  CFSG.KD.W4RowLane.Ly.ly_dih67

end Certificates

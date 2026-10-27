module

public import Certificates.Data.L34QEight
import Certificates.Kernel.L34QEight.K642001
import Certificates.Kernel.L34QEight.K642001B
import Certificates.Kernel.L34QEight.K642001C
import CFSG.Certificates.Kernel.L34QEightKSound

namespace Certificates

open CFSG.Certificates.Kernel.L34QEightK

theorem blocks642001 (j : Nat) (hj : j < 21) : ch642001b j = true := by
  interval_cases j
  exacts [ch642001b0, ch642001b1, ch642001b2, ch642001b3, ch642001b4, ch642001b5, ch642001b6,
    ch642001b7, ch642001b8, ch642001b9, ch642001b10, ch642001b11, ch642001b12, ch642001b13,
    ch642001b14, ch642001b15, ch642001b16, ch642001b17, ch642001b18, ch642001b19, ch642001b20]

end Certificates

public section

namespace Certificates

open CFSG.Certificates.Kernel.L34QEightK

theorem certificate642001 : Certificates.Data.L34QEight.qClosed = true ∧
    Certificates.Data.L34QEight.closureCheck = true :=
  ⟨qClosed_of_qClosedV qClosedV642001,
    closureCheck_of_blocks fun j hj => by
      rw [len642001] at hj
      exact blocks642001 j hj⟩

end Certificates

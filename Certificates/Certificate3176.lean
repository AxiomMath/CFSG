module

public import CFSG.Monster.B.CTIB.VisibleOctadInputs
import Certificates.Kernel.MonsterB.OctFix
public import CFSG.Monster.B.TwoA.Census.CosetEnumBits

public section

open CFSG.Monster CFSG.Monster.B

namespace CertificateChecks.Batch3176

open CFSG.Monster CFSG.Monster.B

theorem octTab_two : AxisCount.Native.octTab[2]! = 3 := by decide +kernel

theorem evenTab_zero : AxisCount.Native.evenTab[0]! = 0 := by decide +kernel

@[expose] def label (a m : ℕ) : Model.Pauli :=
  ⟨false, AxisCount.Native.octCodeG a m, Model.thetaN (AxisCount.Native.octCodeG a m) ^^^
    Model.dualN (AxisCount.Native.spreadG (Model.wordN a) m)⟩

theorem label_eq : label 3 0 = (false, 3, 60) := by decide +kernel

theorem label_ne : label 3 0 ≠ (false, 3, 61) := by decide +kernel

theorem label_three_sixty :
    (⟨false, AxisCount.Native.octCodeG AxisCount.Native.octTab[2]!
      AxisCount.Native.evenTab[0]!, Model.thetaN (AxisCount.Native.octCodeG
        AxisCount.Native.octTab[2]! AxisCount.Native.evenTab[0]!) ^^^
          Model.dualN (AxisCount.Native.spreadG (Model.wordN AxisCount.Native.octTab[2]!)
            AxisCount.Native.evenTab[0]!)⟩ : Model.Pauli) = (false, 3, 60) := by
  rw [octTab_two, evenTab_zero]
  exact label_eq

end CertificateChecks.Batch3176

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.CTIB CFSG.Monster.B.TwoA.Census CFSG.Monster CFSG.Monster.B in
theorem certificate3176 : (octFixCount (tT 1) (tD 1) = 2 ^ 24)
    ∧ ((⟨false, AxisCount.Native.octCodeG AxisCount.Native.octTab[2]!
       AxisCount.Native.evenTab[0]!, Model.thetaN (AxisCount.Native.octCodeG
         AxisCount.Native.octTab[2]! AxisCount.Native.evenTab[0]!) ^^^
           Model.dualN (AxisCount.Native.spreadG (Model.wordN AxisCount.Native.octTab[2]!)
             AxisCount.Native.evenTab[0]!)⟩ : Model.Pauli) = (false, 3, 60)) :=
  ⟨OctFix.octFixCount_eq, CertificateChecks.Batch3176.label_three_sixty⟩

end Certificates

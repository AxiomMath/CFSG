module

public import CFSG.RankThree.PartOne.KS.LyFiveInputs
import Certificates.Kernel.LyFive.Assembly

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne.LyFive in
theorem certificate14967 : lyXClassOK = true ∧ lyY3ClassOK = true ∧ lyYCommOK = true :=
  ⟨KernelLyFive.lyXClass, KernelLyFive.lyY3Class, KernelSporSch.LyFC.lyYComm⟩

end Certificates

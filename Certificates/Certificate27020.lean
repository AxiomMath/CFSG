module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HSFixData
import Certificates.Kernel.TwoHS.F27020Facts
import Certificates.Kernel.TwoHS.F27020R
import Certificates.Kernel.TwoHS.F27020Q0
import Certificates.Kernel.TwoHS.F27020Q1
import Certificates.Kernel.TwoHS.F27020Q2
import Certificates.Kernel.TwoHS.F27020Q3

public section

namespace Certificates

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate27020 : hfxOK = true :=
  CFSG.KD.TwoHS.hfxOK_of CFSG.KD.TwoHS.ok27020R fun i => by
    fin_cases i
    · exact CFSG.KD.TwoHS.ok27020Q_0
    · exact CFSG.KD.TwoHS.ok27020Q_1
    · exact CFSG.KD.TwoHS.ok27020Q_2
    · exact CFSG.KD.TwoHS.ok27020Q_3

end Certificates

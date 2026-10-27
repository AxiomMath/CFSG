
module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Basic
public import CFSG.Alternating.Multipliers.SpinCover
import Certificates.Kernel.SpinOrb.Assembly

public section

namespace Certificates

theorem certificate13002 : CFSG.ComponentClassification.Sol76.Sig.GSYard02.SylowFourJoined
    (CFSG.Alternating.Multipliers.Spin.E 9) := CFSG.KD.SpinOrb.sylowE9

end Certificates

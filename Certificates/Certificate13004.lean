
module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Basic
public import CFSG.Alternating.Multipliers.SpinCover
import Certificates.Kernel.SpinOrb.Assembly

public section

namespace Certificates

theorem certificate13004 : CFSG.ComponentClassification.Sol76.Sig.GSYard02.SylowFourJoined
    (CFSG.Alternating.Multipliers.Spin.E 11) := CFSG.KD.SpinOrb.sylowE11

end Certificates

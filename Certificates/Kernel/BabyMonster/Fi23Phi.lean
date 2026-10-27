module

public import Certificates.Kernel.BabyMonster.Fi23Fu
public import Certificates.Kernel.Sporadic.Fi23Fu.Rels
public import Certificates.Kernel.Sporadic.Fi23Fu.Checks
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.Fi23Br.Checks
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Spor.OrdSound
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.BabyMonster.Fi23Phi.All
public import CFSG.Sporadic.Co2Schreier.ThirdChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelBM.Fi23Phi

open CFSG.KC.BM CFSG.Sporadic.GLQ CertificateChecks.KernelBM.Fi23InB CertificateChecks.KernelBM.Fi23Fu CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

local notation "sm" => stripMat

end CertificateChecks.KernelBM.Fi23Phi

end

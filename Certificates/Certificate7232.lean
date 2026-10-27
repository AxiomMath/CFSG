
module

public import CFSG.Quasithin.Vol2.KGFactC31RuCand
import Certificates.Kernel.Misc.RuScan.Cand
import CFSG.Sporadic.Schreier.RuCheckBasicInputs
import CFSG.Sporadic.Schreier.RuCheckChainsInputs
import CFSG.Sporadic.Schreier.RuCheckLInputs
meta import CFSG.Sporadic.Schreier.RuCheckChains
meta import CFSG.Sporadic.Schreier.RuWitArrays
import CFSG.Sporadic.Schreier.RuArrays
import CFSG.Certificates.NativeSetOrbit
import CFSG.Sporadic.Schreier.RuWitArrays
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuBaseBase
public import CFSG.Quasithin.Vol2.KGFactC31RuRefKBase
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.RuLGroup
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

open CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.Ru

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.Ru in
theorem certificate7232 : ∀ i, 4 ≤ i → i < 9 → ∀ c ∈ ruL, cosetH i * c * ruA0 * (cosetH i * c)⁻¹ ≠ ruA0 →
    ∀ es q, (es, q) ∈ ruGroups → CandConcl i (cosetH i * c) ruA0 es q :=
  fun _ hi4 hi _ hc hmv _ _ hes => KernelMisc.RuScan.candFactL hi4 hi hc hmv hes

end Certificates

end

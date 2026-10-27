
module

public import Certificates.Certificate7229Base

public import CFSG.Quasithin.Vol2.KGFactC31RuReps
public import CFSG.Sporadic.Schreier.RuWitDefs
import Certificates.Kernel.Misc.RuCov.Glue
import CFSG.Sporadic.Schreier.RuCheckBasicInputs
import CFSG.Sporadic.Schreier.RuCheckChainsInputs
import CFSG.Sporadic.Schreier.RuCheckInvInputs
meta import CFSG.Sporadic.Schreier.RuTreeEltA
meta import CFSG.Sporadic.Schreier.RuWitArrays
meta import CFSG.Sporadic.Schreier.RuCheckChains
meta import CFSG.Sporadic.Schreier.RuEnum
import CFSG.Sporadic.Schreier.RuCheckLInputs
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
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.RuSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

open CFSG.Quasithin.KGC31.Ru CFSG.Sporadic.RuSchreier

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.KGC31.Ru CFSG.Sporadic.RuSchreier in
theorem certificate7229 : (∀ x ∈ ruC, x ^ 2 = 1 → x ≠ 1 → x ≠ ruZ → ∃ r ∈ repsZG, ∃ c ∈ ruC, c * x * c⁻¹ = r) ∧
    (∀ x ∈ ruL, x ^ 2 = 1 → x ≠ 1 → x ≠ ruA0 → ∃ r ∈ repsAG, ∃ c ∈ ruL, c * x * c⁻¹ = r) ∧
    (∀ w ∈ otherZW, (fixSet (wG w)).ncard = 0) ∧ ∀ w ∈ otherAW, (fixSet (abG w)).ncard = 92 :=
  ⟨fun _ hx h2 h1 hz => KernelMisc.RuCov.coverC hx h2 h1 hz,
    fun _ hx h2 h1 ha => KernelMisc.RuCov.coverL hx h2 h1 ha, KernelMisc.RuCov.fixZ,
    KernelMisc.RuCov.fixA⟩

end Certificates

end

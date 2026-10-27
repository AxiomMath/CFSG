module

public import CFSG.Quasithin.Vol2.KGFactC31HeElt
public import CFSG.Quasithin.Vol2.KGFactC31Orb
public import CFSG.Sporadic.HeldB.InnerRestrict
import CFSG.Sporadic.HeldB.CertPChainData
import Certificates.Data.CFSGNative.Schreier.Check
import CFSG.Sporadic.HeldB.InnerCheckInputs
meta import CFSG.Sporadic.HeldB.InnerData
meta import CFSG.Sporadic.HeldB.Common
meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
import CFSG.Sporadic.HeldB.InnerClassCheckInputs
meta import CFSG.Sporadic.HeldB.HeBlocks
meta import CFSG.Sporadic.HeldB.InnerCheck
meta import Certificates.Data.CFSGNative.HeldB.Tests
meta import Certificates.Data.CFSGNative.PairSchreier.Core
import CFSG.Sporadic.HeldB.OuterArithCheckInputs
meta import CFSG.Sporadic.HeldB.AutData
meta import Certificates.Data.CFSGNative.Schreier.Check
import CFSG.Sporadic.HeldB.HeBlocks
import CFSG.Sporadic.HeldB.OuterArithCheck
import Certificates.Data.CFSGNative.HeldB.Tests
meta import CFSG.Sporadic.HeldB.OuterArithCheck
import Certificates.Kernel.He7222.GlueHcls
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
public import CFSG.Quasithin.Background.C31Insp
public import CFSG.Quasithin.Vol2.KGFactC31Cover
public import CFSG.Quasithin.Vol2.KGFactC31EBasis
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He CFSG.Sporadic.HeldB

public section

namespace Certificates

open CertificateChecks.KernelHe7222

open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He CFSG.Sporadic.HeldB in
theorem certificate7222 : ∀ τ ∈ [heGenPerm 0, heT1P], ∀ y ∈ heP, y * τ * y⁻¹ ≠ τ →
    (∃ e ∈ [25, 343, 17], y ^ e = 1) →
    (∀ j : ℕ, τ * (y ^ j * τ * (y ^ j)⁻¹) = y ^ j * τ * (y ^ j)⁻¹ * τ) →
    ∃ d ∈ heAutGroup, (∀ bw ∈ w5W, d * elt bw * d⁻¹ ∈ orbSub y τ) ∨
      (∀ bw ∈ w7W, d * elt bw * d⁻¹ ∈ orbSub y τ) :=
  fun τ hτ y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl
    · exact a0_hcls y hy
    · exact t1_hcls y hy

end Certificates

end

end

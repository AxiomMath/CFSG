module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighCheck
import Certificates.Kernel.RootOrbit.Graph

public section

open CFSG.HardMathSupport.Timmesfeld.LangTorus TauCeti CertificateChecks.KernelRootOrbit

namespace Certificates

open CFSG.HardMathSupport.Timmesfeld.LangTorus TauCeti in
theorem certificate13660 : dGraphOK (DynkinType.D 5).cartanMatrix ⟨3, by decide⟩ ⟨4, by decide⟩ 40 = true ∧
    dGraphOK (DynkinType.D 6).cartanMatrix ⟨4, by decide⟩ ⟨5, by decide⟩ 60 = true ∧
    dGraphOK (DynkinType.D 7).cartanMatrix ⟨5, by decide⟩ ⟨6, by decide⟩ 84 = true ∧
    dGraphOK (DynkinType.D 8).cartanMatrix ⟨6, by decide⟩ ⟨7, by decide⟩ 112 = true := by
  simp only [DynkinType.cartanMatrix_D]
  exact ⟨dGraphOK_D5, dGraphOK_D6, dGraphOK_D7, dGraphOK_D8⟩

end Certificates

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Stage1Sem
import Certificates.Kernel.RouteP.S1.Glue

public section

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

namespace Certificates

open CertificateChecks

theorem certificate450240 : ∃ y w : Ω, Stage1Sem y w :=
  KernelRouteP.s1_sem

theorem certificate450240.stab_transitive : ∀
    {c : Ω}, Δ.Adj x0 c →
    Δ.Adj x1 c → Δ.Adj x2 c → ∃ h ∈ A1gen, h • x2 = x2 ∧ h • planePt 3 = c :=
  KernelRouteP.s1_stab

end Certificates

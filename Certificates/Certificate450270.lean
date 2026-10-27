module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Dist
import Certificates.Kernel.RouteP.Ronan.Glue

public section

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three
open CertificateChecks.KernelRouteP.Ronan

namespace Certificates

open CertificateChecks

theorem certificate450270 :     (Δ.induce (Δ.commonNeighbors x0 y2)).Preconnected :=
  ronan_Q_connected

theorem certificate450270.P_witness : ∀
    {y : Ω},
    Δ.dist x0 y = 2 → Δ.Adj y2 y → ∃ c, Δ.Adj x0 c ∧ Δ.Adj c y2 ∧ Δ.Adj c y :=
  ronan_P_witness

theorem certificate450270.A3_connected_a :     (Δ.induce {c | Δ.Adj y3a c ∧ Δ.dist x0 c = 2}).Preconnected :=
  ronan_A3_connected_a

theorem certificate450270.A3_connected_b :     (Δ.induce {c | Δ.Adj y3b c ∧ Δ.dist x0 c = 2}).Preconnected :=
  ronan_A3_connected_b

theorem certificate450270.Hp_witness_a : ∀
    {y : Ω},
    Δ.dist x0 y = 3 → Δ.Adj y3a y → ∃ h, Δ.dist x0 h = 2 ∧ Δ.Adj h y3a ∧ Δ.Adj h y :=
  ronan_Hp_witness_a

theorem certificate450270.Hp_witness_b : ∀
    {y : Ω},
    Δ.dist x0 y = 3 → Δ.Adj y3b y → ∃ h, Δ.dist x0 h = 2 ∧ Δ.Adj h y3b ∧ Δ.Adj h y :=
  ronan_Hp_witness_b

theorem certificate450270.H4_connected :     (Δ.induce {c | Δ.Adj x0 c}).Preconnected :=
  ronan_H4_connected

theorem certificate450270.dist_x0_eq_three_of_adj_y4a : ∀
    {y : Ω}, Δ.Adj y4a y → Δ.dist x0 y = 3 :=
  ronan_dist_x0_eq_three_of_adj_y4a

theorem certificate450270.dist_x0_eq_three_of_adj_y4b : ∀
    {y : Ω}, Δ.Adj y4b y → Δ.dist x0 y = 3 :=
  ronan_dist_x0_eq_three_of_adj_y4b

end Certificates

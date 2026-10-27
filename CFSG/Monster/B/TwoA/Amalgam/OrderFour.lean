module

public import CFSG.Monster.B.TwoA.Amalgam.OrderFourCore
public import CFSG.Monster.B.TwoA.Amalgam.DistTwo

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8

theorem native_coset_graph_order_four_common_neighbors :
    (∀ v w : CVert, w ∈ sphereFour v →
      orderOf (clabel v * clabel w) = 4 ∧ (cgraph.commonNeighbors v w).ncard = 648 ∧
      (∃ s : Shat, v ∈ cPi s ∧ w ∈ cPi s) ∧
      (∀ s s' : Shat, v ∈ cPi s → w ∈ cPi s → v ∈ cPi s' → w ∈ cPi s' → cPi s = cPi s') ∧
      ∀ s : Shat, v ∈ cPi s → w ∈ cPi s → cgraph.commonNeighbors v w ⊆ cPi s) ∧
    (∀ v : CVert, (sphereFour v).ncard = 11174042880) ∧
    ∀ v w : cPi0, v ≠ w → ¬ cgraphPi.Adj v w →
      (clabel v * clabel w) ^ 2 = xhat ∧
      ∀ s : Shat, (cvMul v s = v ∧ cvMul w s = w) ↔ (s : Dfull) ∈ Jhat ∧
        (s : Dfull) ∈ Subgroup.centralizer {clabel v} ∧
          (s : Dfull) ∈ Subgroup.centralizer {clabel w} := by
  obtain ⟨-, hpath, hsph, htrans, μ₃, μ₄, -, -, -, hμ₄, hcount⟩ :=
    native_coset_graph_two_distance_two_orbits
  exact order_four_common_neighbors_of hpath (fun v => (hsph v).2.1) htrans
    ⟨μ₄, hμ₄, fun v => (hcount v).2⟩

end CFSG.Monster.B.TwoA.Amalgam

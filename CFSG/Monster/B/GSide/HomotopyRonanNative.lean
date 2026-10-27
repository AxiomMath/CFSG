module

public import CFSG.Monster.B.TwoA.Amalgam.Exact3510
public import CFSG.Monster.B.GSide.HomotopyRonan

public section

namespace CFSG.Monster.B.GSide

open SimpleGraph CFSG.Monster.B.Recog CFSG.Monster.B.TwoA.Amalgam

theorem cgraph_triangulable_of
    (B0 : ∀ x y : CVert, cgraph.dist x y ≤ 3)
    (B24 : ∀ v w : CVert, w ∈ sphereFour v →
      (cgraph.induce (cgraph.commonNeighbors v w)).Connected)
    (B2tri : ∀ v x y : CVert, cgraph.dist v x = 2 → cgraph.dist v y = 2 → cgraph.Adj x y →
      ∃ c, cgraph.Adj v c ∧ cgraph.Adj c x ∧ cgraph.Adj c y)
    (B3loc : ∀ v u c : CVert, cgraph.dist v u = 3 → cgraph.Adj u c → cgraph.dist v c = 2 →
      c ∈ sphereFour v)
    (B3con : ∀ v u : CVert, cgraph.dist v u = 3 →
      (cgraph.induce (cgraph.neighborSet u ∩ sphereFour v)).Connected)
    (B3tri : ∀ v x y : CVert, cgraph.dist v x = 3 → cgraph.dist v y = 3 → cgraph.Adj x y →
      ∃ h, cgraph.dist v h = 2 ∧ cgraph.Adj h x ∧ cgraph.Adj h y) :
    Triangulable cgraph := by
  refine triangulable_of_dist_le_three B0 (fun v w hvw => ?_) B2tri (fun v u hvu => ?_) B3tri
  · have hw : w ∈ sphereThree v ∪ sphereFour v := by
      rw [← (native_coset_graph_two_distance_two_orbits.2.2.1 v).1]
      exact hvw
    rcases hw with hw | hw
    · exact ((native_order_three_common_neighbors_exact_3510.1 v w hw).1).preconnected
    · exact (B24 v w hw).preconnected
  · have e : {c | cgraph.Adj u c ∧ cgraph.dist v c = 2} = cgraph.neighborSet u ∩ sphereFour v := by
      ext c
      exact ⟨fun ⟨huc, hvc⟩ => ⟨huc, B3loc v u c hvu huc hvc⟩, fun ⟨huc, hc⟩ => ⟨huc, hc.1⟩⟩
    rw [e]
    exact (B3con v u hvu).preconnected

end CFSG.Monster.B.GSide

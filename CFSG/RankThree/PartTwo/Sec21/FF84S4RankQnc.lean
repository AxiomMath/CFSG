module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4RankTabQ

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)
open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem Q_noncentralT : ∀ x ∈ rankQ.map FF84.tab,
    (∃ z ∈ rankQ.map FF84.tab, FF84.comp x z ≠ FF84.comp z x) →
    ((rankQ.map FF84.tab).filter (fun z => decide (FF84.comp z x = FF84.comp x z))).length = 16 ∧
      ∃ y ∈ rankQ.map FF84.tab, ∃ w ∈ rankQ.map FF84.tab,
        FF84.comp y x = FF84.comp x y ∧ FF84.comp w x = FF84.comp x w ∧
        FF84.comp y w ≠ FF84.comp w y := by
  rw [rankQ_tab]; decide +kernel

theorem Q_noncentral : ∀ c ∈ rankQ,
    (∃ d ∈ rankQ, FF84.comp (FF84.tab c) (FF84.tab d) ≠ FF84.comp (FF84.tab d) (FF84.tab c)) →
    ((rankQ.filter (fun d => decide (FF84.comp (FF84.tab d) (FF84.tab c) =
        FF84.comp (FF84.tab c) (FF84.tab d)))).length = 16 ∧
      ∃ d ∈ rankQ, ∃ e ∈ rankQ,
        FF84.comp (FF84.tab d) (FF84.tab c) = FF84.comp (FF84.tab c) (FF84.tab d) ∧
        FF84.comp (FF84.tab e) (FF84.tab c) = FF84.comp (FF84.tab c) (FF84.tab e) ∧
        FF84.comp (FF84.tab d) (FF84.tab e) ≠ FF84.comp (FF84.tab e) (FF84.tab d)) := by
  intro c hc hnc
  have hx : FF84.tab c ∈ rankQ.map FF84.tab := List.mem_map.2 ⟨c, hc, rfl⟩
  have hnc' : ∃ z ∈ rankQ.map FF84.tab, FF84.comp (FF84.tab c) z ≠ FF84.comp z (FF84.tab c) := by
    obtain ⟨d, hd, hne⟩ := hnc
    exact ⟨_, List.mem_map.2 ⟨d, hd, rfl⟩, hne⟩
  obtain ⟨hlen, y, hy, w, hw, hyc, hwc, hyw⟩ := Q_noncentralT _ hx hnc'
  obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
  obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
  refine ⟨?_, y', hy', w', hw', hyc, hwc, hyw⟩
  rw [List.filter_map, List.length_map] at hlen
  exact hlen


end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end

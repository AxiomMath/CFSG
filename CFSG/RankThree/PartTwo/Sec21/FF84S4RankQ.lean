module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4RankTabP1
public import CFSG.RankThree.PartTwo.Sec21.FF84S4RankTabP2
public import CFSG.RankThree.PartTwo.Sec21.FF84S4RankTabQ

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)
open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem Q_mul : ∀ x ∈ rankQ.map FF84.tab, ∀ y ∈ rankQ.map FF84.tab,
    FF84.comp x y ∈ rankQ.map FF84.tab := by
  rw [rankQ_tab]; decide +kernel
theorem Q_one : FF84.tab 1 ∈ rankQ.map FF84.tab := by
  rw [rankQ_tab]; decide +kernel
theorem Q_inv : ∀ x ∈ rankQ.map FF84.tab, ∃ y ∈ rankQ.map FF84.tab,
    FF84.comp x y = FF84.tab 1 := by
  rw [rankQ_tab]; decide +kernel
theorem Q_nodup : (rankQ.map FF84.tab).Nodup := by
  rw [rankQ_tab]; decide +kernel
theorem Q_of_P12T : ∀ x ∈ rankP1.map FF84.tab, x ∈ rankP2.map FF84.tab →
    x ∈ rankQ.map FF84.tab := by
  rw [rankP1_tab, rankP2_tab, rankQ_tab]; decide +kernel
theorem Q_of_P12 : ∀ c ∈ rankP1, FF84.tab c ∈ rankP2.map FF84.tab →
    FF84.tab c ∈ rankQ.map FF84.tab :=
  fun c hc => Q_of_P12T _ (List.mem_map.2 ⟨c, hc, rfl⟩)
theorem Q_center : ∀ x ∈ rankQ.map FF84.tab,
    (∀ y ∈ rankQ.map FF84.tab, FF84.comp x y = FF84.comp y x) →
      x = FF84.tab 1 ∨ x = FF84.tab rep4 := by
  rw [rankQ_tab, rep4_tab]; decide +kernel
theorem Q_nonab : ∃ c ∈ rankQ, ∃ d ∈ rankQ,
    FF84.comp (FF84.tab c) (FF84.tab d) ≠ FF84.comp (FF84.tab d) (FF84.tab c) := by
  decide +kernel

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end

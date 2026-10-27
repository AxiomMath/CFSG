module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4RankTabP1

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)
open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem P1_mul : ∀ x ∈ rankP1.map FF84.tab, ∀ y ∈ rankP1.map FF84.tab,
    FF84.comp x y ∈ rankP1.map FF84.tab := by
  rw [rankP1_tab]; decide +kernel
theorem P1_one : FF84.tab 1 ∈ rankP1.map FF84.tab := by
  rw [rankP1_tab]; decide +kernel
theorem P1_inv : ∀ x ∈ rankP1.map FF84.tab, ∃ y ∈ rankP1.map FF84.tab,
    FF84.comp x y = FF84.tab 1 := by
  rw [rankP1_tab]; decide +kernel
theorem P1_nodup : (rankP1.map FF84.tab).Nodup := by
  rw [rankP1_tab]; decide +kernel
theorem P1_commT : ∀ x ∈ rankP1.map FF84.tab, FF84.comp x (FF84.tab rep4) =
    FF84.comp (FF84.tab rep4) x := by
  rw [rankP1_tab, rep4_tab]; decide +kernel
theorem P1_comm : ∀ c ∈ rankP1, FF84.comp (FF84.tab c) (FF84.tab rep4) =
    FF84.comp (FF84.tab rep4) (FF84.tab c) :=
  fun c hc => P1_commT _ (List.mem_map.2 ⟨c, hc, rfl⟩)
theorem P1_sign : ∀ c ∈ rankP1, Equiv.Perm.sign c = 1 := by
  simp [rankP1, Equiv.Perm.sign_swap']


end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end

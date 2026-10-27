module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4RankTabP2

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)
open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem P2_mul : ∀ x ∈ rankP2.map FF84.tab, ∀ y ∈ rankP2.map FF84.tab,
    FF84.comp x y ∈ rankP2.map FF84.tab := by
  rw [rankP2_tab]; decide +kernel
theorem P2_one : FF84.tab 1 ∈ rankP2.map FF84.tab := by
  rw [rankP2_tab]; decide +kernel
theorem P2_inv : ∀ x ∈ rankP2.map FF84.tab, ∃ y ∈ rankP2.map FF84.tab,
    FF84.comp x y = FF84.tab 1 := by
  rw [rankP2_tab]; decide +kernel
theorem P2_nodup : (rankP2.map FF84.tab).Nodup := by
  rw [rankP2_tab]; decide +kernel
theorem P2_commT : ∀ x ∈ rankP2.map FF84.tab, FF84.comp x (FF84.tab rep4) =
    FF84.comp (FF84.tab rep4) x := by
  rw [rankP2_tab, rep4_tab]; decide +kernel
theorem P2_comm : ∀ c ∈ rankP2, FF84.comp (FF84.tab c) (FF84.tab rep4) =
    FF84.comp (FF84.tab rep4) (FF84.tab c) :=
  fun c hc => P2_commT _ (List.mem_map.2 ⟨c, hc, rfl⟩)
theorem P2_sign : ∀ c ∈ rankP2, Equiv.Perm.sign c = 1 := by
  simp [rankP2, Equiv.Perm.sign_swap']


end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end

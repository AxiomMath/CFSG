module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenCores

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven

attribute [local irreducible] dotProduct

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.RankThree.Native.ONTriple Subgroup

set_option linter.unusedSectionVars false

@[expose] def LSub (j k : ℕ) : Subgroup GM := Subgroup.closure (Set.range (lY j k))

theorem LSub_ne_bot {j k : ℕ} (hj : j < 2) (hk : k < 9) :
    LSub j k ≠ ⊥ := by
  intro h
  have hx : xE j 0 (rowAt j k 0) 0 ∈ LSub j k :=
    xE_mem_Lk (j := j) (k := k) hj hk (l := 0) (i := 0) (by norm_num) (by norm_num)
  rw [h, Subgroup.mem_bot] at hx
  exact xE_ne_one hj (rowAt_lt j hj k hk 0 (by norm_num)) (i := 0) (by norm_num) hx

theorem isSimpleGroup_LSub
    {j k : ℕ} (hj : j < 2) (hk : k < 9) :
    IsSimpleGroup ↥(LSub j k) := by
  obtain ⟨y, hy, hcl⟩ := exists_rels_lY hj hk
  exact isSimpleGroup_closure y hy hcl (LSub_ne_bot hj hk)

theorem card_LSub
    {j k : ℕ} (hj : j < 2) (hk : k < 9) :
    Nat.card (LSub j k) = 1876896 := by
  obtain ⟨y, hy, hcl⟩ := exists_rels_lY hj hk
  exact card_closure_eq y hy hcl (LSub_ne_bot hj hk)

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven

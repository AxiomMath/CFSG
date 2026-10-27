
module

public import CFSG.Sporadic.Fi23.ClassBase

public section

namespace CFSG.Sporadic.Fi23

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem zmod3_pow253 : ∀ c : ZMod 3, c ^ 253 = 1 → c = 1 := by decide

theorem chainBase_size : chainBase.size = 6 := rfl

theorem chainBase_zero : chainBase[0]! = 0 := by decide

theorem chainBase_one : chainBase[1]! = 1 := by decide

theorem chainWords_size : chainWords.size = 12 := by decide

noncomputable abbrev root : Fin 31671 := ⟨0, by norm_num⟩

@[expose] def InTree (T : Tree) (p : ℕ) : Prop :=
  ap T.pos p < T.pts.size ∧ ap T.pts (ap T.pos p) = p

instance (T : Tree) (p : ℕ) : Decidable (InTree T p) := by unfold InTree; infer_instance

theorem inTreeB_iff (T : Tree) (p : ℕ) : inTreeB T p = true ↔ InTree T p := by
  simp [inTreeB, InTree]

@[expose] noncomputable def subLab (p : Fin 31671) : Fin 3 :=
  if p.val = 0 then 0 else if InTree trees[1]! p.val then 1 else 2

theorem subLab_eq_zero {p : Fin 31671} : subLab p = 0 ↔ p = root := by
  unfold subLab
  constructor
  · intro h
    by_contra hp
    have hp' : p.val ≠ 0 := fun e => hp (Fin.ext e)
    rw [ite_eq_right hp'] at h
    split_ifs at h <;> exact absurd h (by decide)
  · rintro rfl; simp

theorem card_subLab_zero :
    (Finset.univ.filter (fun p : Fin 31671 => subLab p = 0)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨root, ?_⟩
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact subLab_eq_zero

@[expose] def subSizes : Fin 3 → ℕ := ![1, 3510, 28160]

theorem subSizes_blocks : ∀ S : Finset (Fin 3), (0 : Fin 3) ∈ S →
    (∑ i ∈ S, subSizes i) ∣ 31671 → S = {0} ∨ S = Finset.univ := by
  decide

end CFSG.Sporadic.Fi23

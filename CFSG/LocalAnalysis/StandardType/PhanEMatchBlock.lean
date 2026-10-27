module

public import CFSG.LocalAnalysis.StandardType.PhanEMatchCode
public import CFSG.LocalAnalysis.StandardType.PhanEFlagCut

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

namespace PhanCode

open CFSG.ClassicalInvolution.Phan.PhanE.Flag

@[expose] def IsFlagCode : PhanCode → Prop
  | a1far | a1moved | a2chamber | a2panel | a2coll | a2pol => True
  | a3_1111 | a3_211 | a3_121 | a3_22p | a3_22x | a3_13c | a3_13p | a3_4c | a3_4p => True
  | exchA1A1 | exchA2A1 | prod _ _ => False

@[expose] def cut : PhanCode → List ℕ
  | a1far => [0, 1, 2]
  | a1moved => [0, 2]
  | a2chamber => [0, 1, 2, 3]
  | a2panel => [0, 1, 3]
  | a2coll => [0, 3]
  | a2pol => [0, 3]
  | a3_1111 => [0, 1, 2, 3, 4]
  | a3_211 => [0, 2, 3, 4]
  | a3_121 => [0, 1, 3, 4]
  | a3_22p => [0, 2, 4]
  | a3_22x => [0, 2, 4]
  | a3_13c => [0, 1, 4]
  | a3_13p => [0, 1, 4]
  | a3_4c => [0, 4]
  | a3_4p => [0, 4]
  | _ => []

@[expose] def polB : PhanCode → Bool
  | a2pol | a3_13p | a3_4p => true
  | _ => false

@[expose] def blockPerm : (c : PhanCode) → Equiv.Perm (Fin (c.rank + 1))
  | a2pol => Equiv.swap 0 2
  | a3_22x => Equiv.swap 0 2 * Equiv.swap 1 3
  | a3_13p => Equiv.swap 1 3
  | a3_4p => Equiv.swap 0 3 * Equiv.swap 1 2
  | _ => 1

theorem isCut_cut {c : PhanCode} (hc : c.IsFlagCode) : IsCut (c.rank + 1) c.cut := by
  cases c <;> simp only [IsFlagCode] at hc
  all_goals
    first
    | exact hc.elim
    | exact ⟨by decide, by decide, by
        intro i hi
        simp [cut] at hi
        have h4 : i < 4 := by omega
        interval_cases i <;> first | omega | decide⟩

theorem coreN_iff_cutTypes {c : PhanCode} (hc : c.IsFlagCode) (k : Fin c.rank) :
    c.coreN k = true ↔ k ∈ cutTypes c.rank c.cut := by
  cases c <;> simp only [IsFlagCode] at hc
  all_goals
    first
    | exact hc.elim
    | (fin_cases k <;>
        simp only [cutTypes, Set.mem_setOf_eq] <;>
        rw [Nat.forall_lt_iff_fin] <;>
        decide)

theorem blockPerm_invol (c : PhanCode) (i : Fin (c.rank + 1)) :
    c.blockPerm (c.blockPerm i) = i := by
  cases c <;>
    first
    | (fin_cases i <;> decide)
    | (simp [blockPerm])

theorem blockPerm_spec {c : PhanCode} (hc : c.IsFlagCode) (k : Fin c.rank)
    (hk : c.coreN k = true) :
    ∃ k' : Fin c.rank, k'.val = c.permN k ∧
      (if c.polB = true then
        c.blockPerm k.succ = k'.castSucc ∧ c.blockPerm k.castSucc = k'.succ
      else c.blockPerm k.castSucc = k'.castSucc ∧ c.blockPerm k.succ = k'.succ) := by
  cases c <;> simp only [IsFlagCode] at hc
  all_goals
    first
    | exact hc.elim
    | (fin_cases k <;>
        first
        | exact absurd hk (by decide)
        | decide)

end PhanCode

end CFSG.ClassicalInvolution.Phan.PhanE

end

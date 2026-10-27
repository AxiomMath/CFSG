module

public import CFSG.LocalAnalysis.StandardType.PhanEMatchBlock
public import CFSG.LocalAnalysis.StandardType.PhanEMatchFin

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

namespace PhanCode

@[expose] def IsNode (c : PhanCode) : Prop := c = a1far ∨ c = a1moved

@[expose] def IsPath2 (c : PhanCode) : Prop :=
  c = a2chamber ∨ c = a2panel ∨ c = a2coll ∨ c = a2pol

@[expose] def IsPath3 (c : PhanCode) : Prop :=
  c = a3_1111 ∨ c = a3_211 ∨ c = a3_121 ∨ c = a3_22p ∨ c = a3_22x ∨ c = a3_13c ∨ c = a3_13p ∨
    c = a3_4c ∨ c = a3_4p

theorem IsNode.isFlagCode {c : PhanCode} (h : c.IsNode) : c.IsFlagCode := by
  rcases h with rfl | rfl <;> simp [IsFlagCode]

theorem IsPath2.isFlagCode {c : PhanCode} (h : c.IsPath2) : c.IsFlagCode := by
  rcases h with rfl | rfl | rfl | rfl <;> simp [IsFlagCode]

theorem IsPath3.isFlagCode {c : PhanCode} (h : c.IsPath3) : c.IsFlagCode := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [IsFlagCode]

theorem IsNode.rank {c : PhanCode} (h : c.IsNode) : c.rank = 1 := by
  rcases h with rfl | rfl <;> rfl

theorem IsPath2.rank {c : PhanCode} (h : c.IsPath2) : c.rank = 2 := by
  rcases h with rfl | rfl | rfl | rfl <;> rfl

theorem IsPath3.rank {c : PhanCode} (h : c.IsPath3) : c.rank = 3 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

inductive Shape2 : PhanCode → Prop
  | path {c : PhanCode} : c.IsPath2 → Shape2 c
  | exch : Shape2 exchA1A1
  | nodes {a b : PhanCode} : a.IsNode → b.IsNode → Shape2 (prod a b)

inductive Shape3 : PhanCode → Prop
  | path {c : PhanCode} : c.IsPath3 → Shape3 c
  | exchPencil : Shape3 exchA2A1
  | pathNode {a b : PhanCode} : a.IsPath2 → b.IsNode → Shape3 (prod a b)
  | exchNode {b : PhanCode} : b.IsNode → Shape3 (prod exchA1A1 b)
  | nodes3 {a b b' : PhanCode} : a.IsNode → b.IsNode → b'.IsNode → Shape3 (prod (prod a b) b')

private lemma plh_isNode_of_mem {c : PhanCode} (h : c ∈ Match.codes1) : c.IsNode := by
  simp only [Match.codes1, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with h1 | h2
  · subst h1; exact Or.inl rfl
  · subst h2; exact Or.inr rfl

theorem Shape2.of_mem {c : PhanCode} (h : c ∈ Match.codes2) : Shape2 c := by
  simp only [Match.codes2] at h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with h1 | h2 | h3 | h4 | h5
    · subst h1; exact Shape2.path (by simp [IsPath2])
    · subst h2; exact Shape2.path (by simp [IsPath2])
    · subst h3; exact Shape2.path (by simp [IsPath2])
    · subst h4; exact Shape2.path (by simp [IsPath2])
    · subst h5; exact Shape2.exch
  · rcases List.mem_flatMap.mp h with ⟨a, ha, h⟩
    rcases List.mem_map.mp h with ⟨b, hb, hbc⟩
    subst hbc
    exact Shape2.nodes (plh_isNode_of_mem ha) (plh_isNode_of_mem hb)

theorem Shape3.of_mem {c : PhanCode} (h : c ∈ Match.codes3) : Shape3 c := by
  simp only [Match.codes3] at h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
    · subst h1; exact Shape3.path (by simp [IsPath3])
    · subst h2; exact Shape3.path (by simp [IsPath3])
    · subst h3; exact Shape3.path (by simp [IsPath3])
    · subst h4; exact Shape3.path (by simp [IsPath3])
    · subst h5; exact Shape3.path (by simp [IsPath3])
    · subst h6; exact Shape3.path (by simp [IsPath3])
    · subst h7; exact Shape3.path (by simp [IsPath3])
    · subst h8; exact Shape3.path (by simp [IsPath3])
    · subst h9; exact Shape3.path (by simp [IsPath3])
    · subst h10; exact Shape3.exchPencil
  · rcases List.mem_flatMap.mp h with ⟨a, ha, h⟩
    rcases List.mem_map.mp h with ⟨b, hb, hbc⟩
    subst hbc
    have h2 := Shape2.of_mem ha
    cases h2 with
    | path hc => exact Shape3.pathNode hc (plh_isNode_of_mem hb)
    | exch => exact Shape3.exchNode (plh_isNode_of_mem hb)
    | nodes ha' hb' => exact Shape3.nodes3 ha' hb' (plh_isNode_of_mem hb)

private theorem plh_permN_lt : (c : PhanCode) → ∀ i : ℕ, i < c.rank → c.permN i < c.rank
  | prod c c' => by
      intro i hi
      change i < c.rank + c'.rank at hi
      show (if i < c.rank then c.permN i else c.rank + c'.permN (i - c.rank)) <
        c.rank + c'.rank
      split_ifs with h
      · have := plh_permN_lt c i h
        omega
      · have h' : i - c.rank < c'.rank := by omega
        have := plh_permN_lt c' (i - c.rank) h'
        omega
  | a1far | a1moved | a2chamber | a2panel | a2coll | a2pol | a3_1111 | a3_211 | a3_121 |
      a3_22p | a3_22x | a3_13c | a3_13p | a3_4c | a3_4p | exchA1A1 | exchA2A1 => by
      intro i hi
      simp only [rank] at hi
      interval_cases i <;> decide

theorem permN_lt (c : PhanCode) {i : ℕ} (hi : i < c.rank) : c.permN i < c.rank :=
  plh_permN_lt c i hi

theorem coxN_prod_left (c c' : PhanCode) {i j : ℕ} (hi : i < c.rank) (hj : j < c.rank) :
    (prod c c').coxN i j = c.coxN i j := by
  show (if i < c.rank ∧ j < c.rank then c.coxN i j else
    if c.rank ≤ i ∧ c.rank ≤ j then c'.coxN (i - c.rank) (j - c.rank) else 2) = c.coxN i j
  rw [if_pos ⟨hi, hj⟩]

theorem coxN_prod_cross (c c' : PhanCode) {i j : ℕ} (hi : i < c.rank) :
    (prod c c').coxN i (c.rank + j) = 2 := by
  show (if i < c.rank ∧ c.rank + j < c.rank then c.coxN i (c.rank + j) else
    if c.rank ≤ i ∧ c.rank ≤ c.rank + j then c'.coxN (i - c.rank) ((c.rank + j) - c.rank)
      else 2) = 2
  rw [if_neg (by omega), if_neg (by omega)]

theorem coreN_prod_left (c c' : PhanCode) {i : ℕ} (hi : i < c.rank) :
    (prod c c').coreN i = c.coreN i := by
  show (if i < c.rank then c.coreN i else c'.coreN (i - c.rank)) = c.coreN i
  rw [if_pos hi]

theorem coreN_prod_right (c c' : PhanCode) (i : ℕ) :
    (prod c c').coreN (c.rank + i) = c'.coreN i := by
  show (if c.rank + i < c.rank then c.coreN (c.rank + i) else
    c'.coreN ((c.rank + i) - c.rank)) = c'.coreN i
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem permN_prod_left (c c' : PhanCode) {i : ℕ} (hi : i < c.rank) :
    (prod c c').permN i = c.permN i := by
  show (if i < c.rank then c.permN i else c.rank + c'.permN (i - c.rank)) = c.permN i
  rw [if_pos hi]

theorem permN_prod_right (c c' : PhanCode) (i : ℕ) :
    (prod c c').permN (c.rank + i) = c.rank + c'.permN i := by
  show (if c.rank + i < c.rank then c.permN (c.rank + i) else
    c.rank + c'.permN ((c.rank + i) - c.rank)) = c.rank + c'.permN i
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

end PhanCode

end CFSG.ClassicalInvolution.Phan.PhanE

end

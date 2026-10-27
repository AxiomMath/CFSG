module

public import CFSG.LocalAnalysis.StandardType.GGHalfX0Kernel

public section

namespace CFSG.StandardType

private def ggHalfX0Sound_bstElems : GGHalfX0BST → List ℕ
  | .leaf => []
  | .node l x r => ggHalfX0Sound_bstElems l ++ [x] ++ ggHalfX0Sound_bstElems r

private def ggHalfX0Sound_BstInv : GGHalfX0BST → Prop
  | .leaf => True
  | .node l x r =>
      ggHalfX0Sound_BstInv l ∧ ggHalfX0Sound_BstInv r ∧
        (∀ y, y ∈ ggHalfX0Sound_bstElems l → y < x) ∧
        (∀ y, y ∈ ggHalfX0Sound_bstElems r → x < y)

private theorem ggHalfX0Sound_mem_bstElems_node (l : GGHalfX0BST) (x : ℕ)
    (r : GGHalfX0BST) (y : ℕ) :
    y ∈ ggHalfX0Sound_bstElems (.node l x r) ↔
      y ∈ ggHalfX0Sound_bstElems l ∨ y = x ∨ y ∈ ggHalfX0Sound_bstElems r := by
  simp only [ggHalfX0Sound_bstElems, List.mem_append, List.mem_singleton]
  tauto

private theorem ggHalfX0Sound_insertCheck (t : GGHalfX0BST) (a : ℕ) (t' : GGHalfX0BST)
    (h : ggHalfX0BSTInsertCheck t a = some t') (hinv : ggHalfX0Sound_BstInv t) :
    a ∉ ggHalfX0Sound_bstElems t ∧ ggHalfX0Sound_BstInv t' ∧
      (∀ y, y ∈ ggHalfX0Sound_bstElems t' ↔ y = a ∨ y ∈ ggHalfX0Sound_bstElems t) := by
  revert h hinv
  induction t generalizing t' with
  | leaf =>
      intro h hinv
      simp only [ggHalfX0BSTInsertCheck, Option.some.injEq] at h
      subst h
      refine ⟨by simp [ggHalfX0Sound_bstElems], ?_, ?_⟩
      · simp [ggHalfX0Sound_BstInv, ggHalfX0Sound_bstElems]
      · intro y
        simp [ggHalfX0Sound_bstElems]
  | node l x r ihl ihr =>
      intro h hinv
      simp only [ggHalfX0BSTInsertCheck] at h
      by_cases hax : a < x
      · rw [if_pos hax] at h
        cases hl : ggHalfX0BSTInsertCheck l a with
        | none => rw [hl] at h; simp at h
        | some l' =>
            rw [hl] at h
            simp only [Option.some.injEq] at h
            subst h
            obtain ⟨hinvl, hinvr, hlt, hgt⟩ := hinv
            obtain ⟨hnotl, hinvl', hmeml⟩ := ihl l' hl hinvl
            refine ⟨?_, ?_, ?_⟩
            · intro hmem
              rw [ggHalfX0Sound_mem_bstElems_node] at hmem
              rcases hmem with hmem | hmem | hmem
              · exact hnotl hmem
              · omega
              · exact absurd (hgt a hmem) (not_lt.mpr (le_of_lt hax))
            · refine ⟨hinvl', hinvr, ?_, hgt⟩
              intro y hy
              rw [hmeml y] at hy
              rcases hy with hya | hy
              · rw [hya]; exact hax
              · exact hlt y hy
            · intro y
              simp only [ggHalfX0Sound_mem_bstElems_node, hmeml y]
              tauto
      · rw [if_neg hax] at h
        by_cases hxa : x < a
        · rw [if_pos hxa] at h
          cases hr : ggHalfX0BSTInsertCheck r a with
          | none => rw [hr] at h; simp at h
          | some r' =>
              rw [hr] at h
              simp only [Option.some.injEq] at h
              subst h
              obtain ⟨hinvl, hinvr, hlt, hgt⟩ := hinv
              obtain ⟨hnotr, hinvr', hmemr⟩ := ihr r' hr hinvr
              refine ⟨?_, ?_, ?_⟩
              · intro hmem
                rw [ggHalfX0Sound_mem_bstElems_node] at hmem
                rcases hmem with hmem | hmem | hmem
                · exact absurd (hlt a hmem) (not_lt.mpr (le_of_lt hxa))
                · omega
                · exact hnotr hmem
              · refine ⟨hinvl, hinvr', ?_, ?_⟩
                · intro y hy; exact hlt y hy
                · intro y hy
                  rw [hmemr y] at hy
                  rcases hy with hya | hy
                  · rw [hya]; exact hxa
                  · exact hgt y hy
              · intro y
                simp only [ggHalfX0Sound_mem_bstElems_node, hmemr y]
                tauto
        · rw [if_neg hxa] at h
          simp at h

private theorem ggHalfX0Sound_checkNodupAux (t : GGHalfX0BST) (l : List ℕ)
    (h : ggHalfX0CheckNodupAux t l = true) (hinv : ggHalfX0Sound_BstInv t) :
    l.Nodup ∧ (∀ x ∈ l, x ∉ ggHalfX0Sound_bstElems t) := by
  revert h hinv
  induction l generalizing t with
  | nil =>
      intro h hinv
      exact ⟨List.nodup_nil, by simp⟩
  | cons v vs ih =>
      intro h hinv
      simp only [ggHalfX0CheckNodupAux] at h
      cases hv : ggHalfX0BSTInsertCheck t v with
      | none => rw [hv] at h; simp at h
      | some t' =>
          rw [hv] at h
          obtain ⟨hnotin, hinv', hmem⟩ := ggHalfX0Sound_insertCheck t v t' hv hinv
          obtain ⟨ihnodup, ihnotin⟩ := ih t' h hinv'
          refine ⟨?_, ?_⟩
          · rw [List.nodup_cons]
            refine ⟨?_, ihnodup⟩
            intro hvmem
            exact ihnotin v hvmem ((hmem v).2 (Or.inl rfl))
          · intro x hx
            rw [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact hnotin
            · intro hxmem
              exact ihnotin x hx ((hmem x).2 (Or.inr hxmem))

private theorem ggHalfX0Sound_checkNodupLenAux (t : GGHalfX0BST) (l : List ℕ) (n : ℕ)
    (h : ggHalfX0CheckNodupLenAux t l n = true) (hinv : ggHalfX0Sound_BstInv t) :
    l.Nodup ∧ l.length = n ∧ (∀ x ∈ l, x ∉ ggHalfX0Sound_bstElems t) := by
  revert h hinv
  induction l generalizing t n with
  | nil =>
      intro h hinv
      cases n with
      | zero => exact ⟨List.nodup_nil, rfl, by simp⟩
      | succ n => simp only [ggHalfX0CheckNodupLenAux] at h; simp at h
  | cons v vs ih =>
      intro h hinv
      cases n with
      | zero => simp only [ggHalfX0CheckNodupLenAux] at h; simp at h
      | succ n =>
          simp only [ggHalfX0CheckNodupLenAux] at h
          cases hv : ggHalfX0BSTInsertCheck t v with
          | none => rw [hv] at h; simp at h
          | some t' =>
              rw [hv] at h
              obtain ⟨hnotin, hinv', hmem⟩ := ggHalfX0Sound_insertCheck t v t' hv hinv
              obtain ⟨ihnodup, ihlen, ihnotin⟩ := ih t' n h hinv'
              refine ⟨?_, ?_, ?_⟩
              · rw [List.nodup_cons]
                exact ⟨fun hvmem => ihnotin v hvmem ((hmem v).2 (Or.inl rfl)), ihnodup⟩
              · simp [ihlen]
              · intro x hx
                rw [List.mem_cons] at hx
                rcases hx with rfl | hx
                · exact hnotin
                · intro hxmem
                  exact ihnotin x hx ((hmem x).2 (Or.inr hxmem))

theorem ggHalfX0CheckDistinctLength_spec {l : List ℕ} {n : ℕ}
    (h : ggHalfX0CheckDistinctLength l n = true) : l.Nodup ∧ l.length = n := by
  unfold ggHalfX0CheckDistinctLength at h
  obtain ⟨h1, h2, _⟩ := ggHalfX0Sound_checkNodupLenAux .leaf l n h trivial
  exact ⟨h1, h2⟩

theorem ggHalfX0CheckNodup_spec {l : List ℕ} (h : ggHalfX0CheckNodup l = true) : l.Nodup := by
  unfold ggHalfX0CheckNodup at h
  exact (ggHalfX0Sound_checkNodupAux .leaf l h trivial).1

private theorem ggHalfX0Sound_mem_insert {a c : ℕ} {l : List ℕ} :
    c ∈ ggHalfX0Insert a l ↔ c = a ∨ c ∈ l := by
  induction l with
  | nil => simp [ggHalfX0Insert]
  | cons b t ih =>
      rw [ggHalfX0Insert]
      by_cases hab : a ≤ b
      · rw [if_pos hab]
        simp only [List.mem_cons]
      · rw [if_neg hab]
        simp only [List.mem_cons]
        rw [ih]
        tauto

private theorem ggHalfX0Sound_insert_perm (a : ℕ) (l : List ℕ) :
    (ggHalfX0Insert a l).Perm (a :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons b t ih =>
      rw [ggHalfX0Insert]
      by_cases hab : a ≤ b
      · rw [if_pos hab]
      · rw [if_neg hab]
        exact (List.Perm.cons b ih).trans (List.Perm.swap a b t)

private theorem ggHalfX0Sound_insert_sorted (a : ℕ) :
    ∀ {l : List ℕ}, l.SortedLE → (ggHalfX0Insert a l).SortedLE := by
  intro l
  induction l with
  | nil =>
      intro _
      rw [ggHalfX0Insert, List.sortedLE_cons]
      exact ⟨by simp, List.sortedLE_nil⟩
  | cons b t ih =>
      intro hl
      rw [List.sortedLE_cons] at hl
      obtain ⟨hb, ht⟩ := hl
      rw [ggHalfX0Insert]
      by_cases hab : a ≤ b
      · rw [if_pos hab, List.sortedLE_cons]
        exact ⟨fun c hc => by
          rw [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact hab
          · exact le_trans hab (hb c hc),
          List.sortedLE_cons.mpr ⟨hb, ht⟩⟩
      · rw [if_neg hab, List.sortedLE_cons]
        have hba : b ≤ a := le_of_lt (not_le.mp hab)
        exact ⟨fun c hc => by
          rw [ggHalfX0Sound_mem_insert] at hc
          rcases hc with hca | hc
          · rw [hca]; exact hba
          · exact hb c hc,
          ih ht⟩

private theorem ggHalfX0Sound_insertSort_perm (l : List ℕ) :
    (ggHalfX0InsertSort l).Perm l := by
  induction l with
  | nil => exact List.Perm.nil
  | cons a t ih =>
      rw [ggHalfX0InsertSort]
      exact (ggHalfX0Sound_insert_perm a (ggHalfX0InsertSort t)).trans (List.Perm.cons a ih)

private theorem ggHalfX0Sound_insertSort_sorted (l : List ℕ) :
    (ggHalfX0InsertSort l).SortedLE := by
  induction l with
  | nil => rw [ggHalfX0InsertSort]; exact List.sortedLE_nil
  | cons a t ih =>
      rw [ggHalfX0InsertSort]
      exact ggHalfX0Sound_insert_sorted a ih

theorem ggHalfX0SubKeyOfBasis_eq_of_mem_iff {b b' : List ℕ}
    (hb : (ggHalfX0SpanMasks b).Nodup) (hb' : (ggHalfX0SpanMasks b').Nodup)
    (h : ∀ v, v ∈ ggHalfX0SpanMasks b ↔ v ∈ ggHalfX0SpanMasks b') :
    ggHalfX0SubKeyOfBasis b = ggHalfX0SubKeyOfBasis b' := by
  have hp : (ggHalfX0SpanMasks b).Perm (ggHalfX0SpanMasks b') :=
    (List.perm_ext_iff_of_nodup hb hb').2 h
  have hperm : (ggHalfX0InsertSort (ggHalfX0SpanMasks b)).Perm
      (ggHalfX0InsertSort (ggHalfX0SpanMasks b')) :=
    (ggHalfX0Sound_insertSort_perm _).trans (hp.trans (ggHalfX0Sound_insertSort_perm _).symm)
  have heq := List.Perm.eq_of_sortedLE (ggHalfX0Sound_insertSort_sorted _)
    (ggHalfX0Sound_insertSort_sorted _) hperm
  unfold ggHalfX0SubKeyOfBasis
  rw [heq]

theorem ggHalfApplyBits_of_zero (A : List ℕ) : ggHalfApplyBits A 0 = 0 := by
  simp [ggHalfApplyBits, Nat.zero_testBit]

theorem ggHalfX0SpanMasks_map_apply (A b : List ℕ) :
    ggHalfX0SpanMasks (b.map (ggHalfApplyBits A)) =
      (ggHalfX0SpanMasks b).map (ggHalfApplyBits A) := by
  induction b with
  | nil => simp [ggHalfX0SpanMasks, ggHalfApplyBits_of_zero]
  | cons v vs ih =>
      rw [List.map_cons, ggHalfX0SpanMasks, ih, ggHalfX0SpanMasks, List.map_append,
        List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro x _
      simp only [Function.comp_apply]
      exact (ggHalfApplyBits_xor A x v).symm

end CFSG.StandardType

end

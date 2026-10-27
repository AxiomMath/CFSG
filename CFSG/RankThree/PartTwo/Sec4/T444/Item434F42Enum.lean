module

public import CFSG.Assembly.Defs
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434F42

open CFSG.Assembly (IsElemAbelian)

variable {G : Type*} [Group G]

@[expose] def wordElt (g : ℕ → G) (w : List ℕ) : G := (w.map g).prod

@[simp] theorem wordElt_nil (g : ℕ → G) : wordElt g [] = 1 := rfl

theorem wordElt_cons (g : ℕ → G) (l : ℕ) (w : List ℕ) :
    wordElt g (l :: w) = g l * wordElt g w := by
  simp [wordElt]

theorem wordElt_append (g : ℕ → G) (w w' : List ℕ) :
    wordElt g (w ++ w') = wordElt g w * wordElt g w' := by
  simp [wordElt]

theorem wordElt_mem {g : ℕ → G} {S : Subgroup G} {r : ℕ} (hS : ∀ l < r, g l ∈ S) {w : List ℕ}
    (hw : ∀ l ∈ w, l < r) : wordElt g w ∈ S :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact hS l (hw l hl)

theorem wordElt_reverse {g : ℕ → G} {r : ℕ} (hg : ∀ l < r, g l * g l = 1) :
    ∀ w : List ℕ, (∀ l ∈ w, l < r) → (wordElt g w)⁻¹ = wordElt g w.reverse
  | [], _ => by simp
  | l :: w, hw => by
    have hl : l < r := hw l (List.mem_cons_self ..)
    have hinv : (g l)⁻¹ = g l := inv_eq_of_mul_eq_one_right (hg l hl)
    rw [wordElt_cons, mul_inv_rev, wordElt_reverse hg w (fun l' hl' => hw l' (List.mem_cons_of_mem
      _ hl')), hinv, List.reverse_cons, wordElt_append]
    simp [wordElt]

theorem isElemAbelian_closure {S : Set G} (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (h3 : ∀ x ∈ S, x ^ 3 = 1) : IsElemAbelian 3 (Subgroup.closure S) :=
  CFSG.Open.IsElemAbelian.closure_of_commute hc h3

theorem enum_spec [Finite G] {g : ℕ → G} {r : ℕ} {L : List (List ℕ)}
    (hL : ∀ w ∈ L, ∀ l ∈ w, l < r) (h1 : ([] : List ℕ) ∈ L)
    (hcl : ∀ w ∈ L, ∀ k < r, ∃ w' ∈ L, wordElt g w' = wordElt g w * g k)
    (hnd : (L.map (wordElt g)).Nodup) :
    (∀ x : G, x ∈ Subgroup.closure (g '' {k | k < r}) ↔ ∃ w ∈ L, wordElt g w = x) ∧
      Nat.card (Subgroup.closure (g '' {k | k < r})) = L.length := by
  set H := Subgroup.closure (g '' {k | k < r}) with hH
  have hgH : ∀ l < r, g l ∈ H := fun l hl => Subgroup.subset_closure ⟨l, hl, rfl⟩
  set S : Set G := {x | ∃ w ∈ L, wordElt g w = x} with hS
  have hS1 : (1 : G) ∈ S := ⟨[], h1, rfl⟩
  have hSmul : ∀ x ∈ S, ∀ k < r, x * g k ∈ S := by
    rintro _ ⟨w, hw, rfl⟩ k hk
    obtain ⟨w', hw', e⟩ := hcl w hw k hk
    exact ⟨w', hw', e⟩
  have hSpow : ∀ x ∈ S, ∀ k < r, ∀ m : ℕ, x * g k ^ m ∈ S := by
    intro x hx k hk m
    induction m with
    | zero => simpa using hx
    | succ m ih =>
      rw [pow_succ, ← mul_assoc]
      exact hSmul _ ih k hk
  have hmem : ∀ x : G, x ∈ H ↔ x ∈ S := by
    intro x
    constructor
    · intro hx
      induction hx using Subgroup.closure_induction_right with
      | one => exact hS1
      | mul_right a _ y hy ih =>
        obtain ⟨k, hk, rfl⟩ := hy
        exact hSmul a ih k hk
      | mul_inv_cancel a _ y hy ih =>
        obtain ⟨k, hk, rfl⟩ := hy
        have hfin : IsOfFinOrder (g k) := isOfFinOrder_of_finite (g k)
        have : (g k)⁻¹ = g k ^ (orderOf (g k) - 1) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hfin.orderOf_pos,
            pow_orderOf_eq_one]
        rw [this]
        exact hSpow a ih k hk _
    · rintro ⟨w, hw, rfl⟩
      exact wordElt_mem hgH (hL w hw)
  refine ⟨fun x => ?_, ?_⟩
  · rw [hmem]
    exact Iff.rfl
  · classical
    have hset : (H : Set G) = ↑(L.map (wordElt g)).toFinset := by
      ext x
      rw [SetLike.mem_coe, hmem, Finset.mem_coe, List.mem_toFinset, List.mem_map]
      exact Iff.rfl
    have hc : Nat.card H = (H : Set G).ncard := Nat.card_coe_set_eq (H : Set G)
    rw [hc, hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map]

end CFSG.RankThree.PartTwo.Sec4.Item434F42

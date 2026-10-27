module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctColl
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctConj

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open scoped Pointwise
open CFSG.GH74.BNPair (chainProd intList)
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley

section Chain

variable {X : Type*} [Group X]

theorem prod_mem_chainProd (A : ℤ → Subgroup X) (f : ℤ → X) :
    ∀ l : List ℤ, (∀ k ∈ l, f k ∈ A k) → (l.map f).prod ∈ chainProd A l
  | [], _ => by simp [chainProd]
  | k :: l, h => by
    simp only [chainProd, List.map_cons, List.prod_cons]
    exact Set.mem_mul.2 ⟨f k, h k (by simp), _,
      prod_mem_chainProd A f l (fun k' hk' => h k' (by simp [hk'])), rfl⟩

theorem exists_fun_of_mem_chainProd_oct (A : ℤ → Subgroup X) :
    ∀ (l : List ℤ), l.Nodup → ∀ x ∈ chainProd A l,
      ∃ f : ℤ → X, (∀ k ∈ l, f k ∈ A k) ∧ x = (l.map f).prod
  | [], _, x, hx => ⟨fun _ => 1, by simp, by simpa [chainProd] using hx⟩
  | k :: l, hnd, x, hx => by
    simp only [chainProd, List.map_cons, List.prod_cons] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx
    have hk : k ∉ l := (List.nodup_cons.1 hnd).1
    obtain ⟨f, hf, rfl⟩ := exists_fun_of_mem_chainProd_oct A l (List.nodup_cons.1 hnd).2 b hb
    refine ⟨Function.update f k a, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj'
      · simpa using ha
      · have hjk : j ≠ k := fun h => hk (h ▸ hj')
        simpa [Function.update_of_ne hjk] using hf j hj'
    · simp only [List.map_cons, List.prod_cons, Function.update_self]
      congr 1
      congr 1
      apply List.map_congr_left
      intro j hj
      have hjk : j ≠ k := fun h => hk (h ▸ hj)
      simp [Function.update_of_ne hjk]

theorem list_map_eq_ofFn {α β : Type*} (l : List α) (f : α → β) :
    l.map f = List.ofFn (fun m : Fin l.length => f (l.get m)) := by
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn]
  rfl

end Chain

section Collection


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

structure OctIntFacts (S : ℤ → ℤ → Set (Fin F4.tag.rank → ℤ)) : Prop where
  mem_S : ∀ i j α, α ∈ S i j ↔ ∃ k : ℤ, i ≤ k ∧ k ≤ j ∧ α ∈ octPos k
  isRoot : ∀ k : ℤ, 1 ≤ k → k ≤ 8 → ∀ α ∈ octPos k, IsRoot F4.tag α ∧ 0 < height α
  closed : ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ 8 → ∀ α ∈ S i j, ∀ β ∈ S i j, ∀ a b : ℕ, 1 ≤ a →
    1 ≤ b → IsRoot F4.tag (a • α + b • β) → a • α + b • β ∈ S i j
  ideal_left : ∀ i j : ℤ, 2 ≤ i → i ≤ j → j ≤ 8 → ∀ α ∈ S (i - 1) j, ∀ β ∈ S i j, ∀ a b : ℕ,
    1 ≤ a → 1 ≤ b → IsRoot F4.tag (a • α + b • β) → a • α + b • β ∈ S i j
  ideal_right : ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ 7 → ∀ α ∈ S i (j + 1), ∀ β ∈ S i j, ∀ a b : ℕ,
    1 ≤ a → 1 ≤ b → IsRoot F4.tag (a • α + b • β) → a • α + b • β ∈ S i j
  disjoint : ∀ k k' : ℤ, 1 ≤ k → k ≤ 8 → 1 ≤ k' → k' ≤ 8 → k ≠ k' → Disjoint (octPos k) (octPos k')
  posBlock : ∀ k : ℤ, 1 ≤ k → k ≤ 8 → octPos k ∈ largeReePosBlocks
  one_eight : S 1 8 = {α | IsRoot F4.tag α ∧ 0 < height α}

theorem octPos_nonempty {k : ℤ} (h1 : 1 ≤ k) (h8 : k ≤ 8) : (octPos k).Nonempty := by
  have hk : k ∈ [1, 2, 3, 4, 5, 6, 7, 8] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  rw [octPos_eq]
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (octLP_ne_nil k hk)
  exact ⟨x, hx⟩

variable {S : ℤ → ℤ → Set (Fin F4.tag.rank → ℤ)}

theorem octPos_injOn (C : OctIntFacts S) {k k' : ℤ} (h1 : 1 ≤ k) (h8 : k ≤ 8) (h1' : 1 ≤ k')
    (h8' : k' ≤ 8) (h : octPos k = octPos k') : k = k' := by
  by_contra hne
  obtain ⟨x, hx⟩ := octPos_nonempty h1 h8
  exact Set.disjoint_left.1 (C.disjoint k k' h1 h8 h1' h8' hne) hx (h ▸ hx)

theorem mem_octRoot_pos {k : ℤ} (hk : 0 < k) {x : Gm K a} :
    x ∈ octRoot K a k ↔ (x : ModGL F4.tag K) ∈ largeReeBlockGroup K a (octPos k) := by
  unfold octRoot
  rw [octBlock_pos hk]
  exact Subgroup.mem_subgroupOf


theorem octColl_list (C : OctIntFacts S) {i j : ℤ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 8)
    {l : List ℤ} (hl : l.Nodup) (hlm : ∀ k, k ∈ l ↔ i ≤ k ∧ k ≤ j) :
    Set.BijOn (fun x : Fin l.length → ModGL F4.tag K => (List.ofFn x).prod)
      (Set.univ.pi fun m => (largeReeBlockGroup K a (octPos (l.get m)) : Set (ModGL F4.tag K)))
      ((rootSpan F4.tag K (S i j) ⊓ F4.reeGamma K a : Subgroup (ModGL F4.tag K)) :
        Set (ModGL F4.tag K)) := by
  have hmem : ∀ m, i ≤ l.get m ∧ l.get m ≤ j := fun m => (hlm _).1 (List.get_mem l m)
  refine octColl_bijOn (S i j) (fun m => octPos (l.get m)) (fun m m' h => ?_)
    (fun m => C.posBlock _ (by have := hmem m; omega) (by have := hmem m; omega)) (fun α => ?_)
    (C.closed i j hi hij hj)
  · have := octPos_injOn C (by have := hmem m; omega) (by have := hmem m; omega)
      (by have := hmem m'; omega) (by have := hmem m'; omega) h
    exact (List.nodup_iff_injective_get.1 hl) this
  · rw [C.mem_S]
    constructor
    · rintro ⟨k, hk1, hk2, hα⟩
      obtain ⟨m, hm⟩ := List.mem_iff_get.1 ((hlm k).2 ⟨hk1, hk2⟩)
      exact ⟨m, hm ▸ hα⟩
    · rintro ⟨m, hα⟩
      exact ⟨l.get m, (hmem m).1, (hmem m).2, hα⟩

end Collection

end CFSG.Quasithin.H13.F431.TwoF4

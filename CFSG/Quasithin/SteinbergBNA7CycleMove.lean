module

public import CFSG.Quasithin.SteinbergBNA7Transvection
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

public noncomputable section

namespace CFSG.Quasithin.SteinbergBN

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}
  (hβ : β.IsAlt) {I : Type*} [DecidableEq I]

@[expose] def indexMove (b : I → V) (p q : I) : I → V :=
  Function.update b q ((transv hβ (b p) : V →ₗ[ZMod 2] V) (b q))

@[expose] def IsIndexMove (b b' : I → V) : Prop := ∃ p q, p ≠ q ∧ b' = indexMove hβ b p q

theorem indexMove_of_ne {b : I → V} {p q i : I} (h : i ≠ q) : indexMove hβ b p q i = b i :=
  Function.update_of_ne h _ _

theorem indexMove_same (b : I → V) (p q : I) :
    indexMove hβ b p q q = (transv hβ (b p) : V →ₗ[ZMod 2] V) (b q) :=
  Function.update_self _ _ _

theorem indexMove_indexMove {b : I → V} {p q : I} (hpq : p ≠ q) :
    indexMove hβ (indexMove hβ b p q) p q = b := by
  funext i
  by_cases hi : i = q
  · subst hi
    rw [indexMove_same, indexMove_of_ne hβ hpq, indexMove_same]
    exact transvLin_transvLin hβ _ _
  · rw [indexMove_of_ne hβ hi, indexMove_of_ne hβ hi]

theorem span_indexMove_le (b : I → V) {p q : I} :
    Submodule.span (ZMod 2) (Set.range (indexMove hβ b p q)) ≤
      Submodule.span (ZMod 2) (Set.range b) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  by_cases hi : i = q
  · subst hi
    rw [indexMove_same, transv_apply]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨i, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩))
  · rw [indexMove_of_ne hβ hi]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem span_indexMove (b : I → V) {p q : I} (hpq : p ≠ q) :
    Submodule.span (ZMod 2) (Set.range (indexMove hβ b p q)) =
      Submodule.span (ZMod 2) (Set.range b) := by
  refine le_antisymm (span_indexMove_le hβ b) ?_
  calc Submodule.span (ZMod 2) (Set.range b) =
      Submodule.span (ZMod 2) (Set.range (indexMove hβ (indexMove hβ b p q) p q)) := by
        rw [indexMove_indexMove hβ hpq]
    _ ≤ _ := span_indexMove_le hβ _

theorem closure_indexMove_le (b : I → V) {p q : I} :
    Subgroup.closure (Set.range fun i => transv hβ (indexMove hβ b p q i)) ≤
      Subgroup.closure (Set.range fun i => transv hβ (b i)) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  by_cases hi : i = q
  · subst hi
    simp only [indexMove_same]
    rw [← conj_transv hβ (transv_isometry hβ (b p))]
    exact mul_mem (mul_mem (Subgroup.subset_closure ⟨p, rfl⟩)
      (Subgroup.subset_closure ⟨i, rfl⟩)) (inv_mem (Subgroup.subset_closure ⟨p, rfl⟩))
  · simp only [indexMove_of_ne hβ hi]
    exact Subgroup.subset_closure ⟨i, rfl⟩

theorem closure_indexMove (b : I → V) {p q : I} (hpq : p ≠ q) :
    Subgroup.closure (Set.range fun i => transv hβ (indexMove hβ b p q i)) =
      Subgroup.closure (Set.range fun i => transv hβ (b i)) := by
  refine le_antisymm (closure_indexMove_le hβ b) ?_
  calc Subgroup.closure (Set.range fun i => transv hβ (b i)) =
      Subgroup.closure (Set.range fun i =>
        transv hβ (indexMove hβ (indexMove hβ b p q) p q i)) := by
        rw [indexMove_indexMove hβ hpq]
    _ ≤ _ := closure_indexMove_le hβ _

theorem reachable_of_adj_reachable {α : Type*} {G H : SimpleGraph α}
    (h : ∀ u v, G.Adj u v → H.Reachable u v) {x y : α} (hxy : G.Reachable x y) :
    H.Reachable x y := by
  obtain ⟨w⟩ := hxy
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

theorem connected_indexMove (b : I → V) {p q : I} (hpq : p ≠ q)
    (hc : (pairGraph hβ b).Connected) : (pairGraph hβ (indexMove hβ b p q)).Connected := by
  have hp : indexMove hβ b p q p = b p := indexMove_of_ne hβ hpq
  have hq : ∀ v, v ≠ q → (pairGraph hβ b).Adj q v →
      (pairGraph hβ (indexMove hβ b p q)).Reachable q v := by
    intro v hvq hadj
    by_cases h : (pairGraph hβ (indexMove hβ b p q)).Adj q v
    · exact h.reachable
    · rw [pairGraph_adj, indexMove_same, indexMove_of_ne hβ hvq, transv_apply,
        LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left] at h
      rw [pairGraph_adj] at hadj
      rw [hadj] at h
      have key : ∀ x y : ZMod 2, 1 + x * y ≠ 1 → x = 1 ∧ y = 1 := by decide
      obtain ⟨h1, h2⟩ := key _ _ h
      have hqp : (pairGraph hβ (indexMove hβ b p q)).Adj q p := by
        rw [pairGraph_adj, indexMove_same, hp]
        have h3 := transv_isometry hβ (b p) (b q) (b p)
        rw [transv_apply_self] at h3
        rw [h3, isAlt_apply_comm hβ]
        exact h1
      by_cases hvp : v = p
      · rw [hvp]
        exact hqp.reachable
      · have hpv : (pairGraph hβ (indexMove hβ b p q)).Adj p v := by
          rw [pairGraph_adj, hp, indexMove_of_ne hβ hvq]
          exact h2
        exact hqp.reachable.trans hpv.reachable
  have key : ∀ u v, (pairGraph hβ b).Adj u v →
      (pairGraph hβ (indexMove hβ b p q)).Reachable u v := by
    intro u v huv
    by_cases hu : u = q
    · subst hu
      exact hq v huv.ne.symm huv
    · by_cases hv : v = q
      · subst hv
        exact (hq u hu huv.symm).symm
      · apply SimpleGraph.Adj.reachable
        rw [pairGraph_adj, indexMove_of_ne hβ hu, indexMove_of_ne hβ hv]
        exact huv
  have : Nonempty I := hc.nonempty
  exact ⟨fun x y => reachable_of_adj_reachable key (hc.preconnected x y)⟩

theorem indexMove_ne_zero (b : I → V) (hb : ∀ i, b i ≠ 0) (p q i : I) :
    indexMove hβ b p q i ≠ 0 := by
  by_cases hi : i = q
  · subst hi
    rw [indexMove_same]
    intro h
    apply hb i
    rw [← transvLin_transvLin hβ (b p) (b i)]
    change (transv hβ (b p) : V →ₗ[ZMod 2] V) ((transv hβ (b p) : V →ₗ[ZMod 2] V) (b i)) = 0
    rw [h, map_zero]
  · rw [indexMove_of_ne hβ hi]
    exact hb i

@[expose] def applyAt (S : Finset I) (g : LinearMap.GeneralLinearGroup (ZMod 2) V) (b : I → V) :
    I → V :=
  fun j => if j ∈ S then (g : V →ₗ[ZMod 2] V) (b j) else b j

theorem rtg_applyAt_transv (b : I → V) (S : Finset I) {p : I} (hp : p ∉ S) :
    Relation.ReflTransGen (IsIndexMove hβ) b (applyAt S (transv hβ (b p)) b) := by
  induction S using Finset.induction_on with
  | empty =>
    have : applyAt ∅ (transv hβ (b p)) b = b := funext fun j => by simp [applyAt]
    rw [this]
  | @insert j S hjS ih =>
    have hpS : p ∉ S := fun h => hp (Finset.mem_insert_of_mem h)
    have hpj : p ≠ j := fun h => hp (h ▸ Finset.mem_insert_self _ _)
    refine (ih hpS).tail ⟨p, j, hpj, ?_⟩
    funext i
    by_cases hij : i = j
    · subst hij
      rw [indexMove_same]
      simp [applyAt, hjS, hpS]
    · rw [indexMove_of_ne hβ hij]
      simp [applyAt, Finset.mem_insert, hij]

@[expose] def pivotProd (b : I → V) (c : ℕ → I) : ℕ → LinearMap.GeneralLinearGroup (ZMod 2) V
  | 0 => 1
  | m + 1 => transv hβ (b (c (m + 1))) * pivotProd b c m

omit [DecidableEq I] in
theorem pivotProd_succ (b : I → V) (c : ℕ → I) (m : ℕ) :
    pivotProd hβ b c (m + 1) = transv hβ (b (c (m + 1))) * pivotProd hβ b c m := rfl

theorem rtg_applyAt_pivotProd (b : I → V) (c : ℕ → I) (S : Finset I) (m : ℕ)
    (hS : ∀ k, 1 ≤ k → k ≤ m → c k ∉ S) :
    Relation.ReflTransGen (IsIndexMove hβ) b (applyAt S (pivotProd hβ b c m) b) := by
  induction m with
  | zero =>
    have : applyAt S (pivotProd hβ b c 0) b = b := funext fun j => by
      simp [applyAt, pivotProd]
    rw [this]
  | succ m ih =>
    have h1 := ih fun k hk1 hkm => hS k hk1 (by omega)
    have hcm : applyAt S (pivotProd hβ b c m) b (c (m + 1)) = b (c (m + 1)) := by
      simp [applyAt, hS (m + 1) (by omega) le_rfl]
    have h2 := rtg_applyAt_transv hβ (applyAt S (pivotProd hβ b c m) b) S
      (hS (m + 1) (by omega) le_rfl)
    rw [hcm] at h2
    have e : applyAt S (pivotProd hβ b c (m + 1)) b =
        applyAt S (transv hβ (b (c (m + 1)))) (applyAt S (pivotProd hβ b c m) b) := by
      funext j
      by_cases hj : j ∈ S <;> simp [applyAt, pivotProd_succ, hj]
    rw [e]
    exact h1.trans h2

omit [DecidableEq I] in
theorem pivotProd_mem_isometryGroup (b : I → V) (c : ℕ → I) (m : ℕ) :
    pivotProd hβ b c m ∈ isometryGroup β := by
  induction m with
  | zero => exact one_mem _
  | succ m ih => exact mul_mem (transv_mem_isometryGroup hβ _) ih

omit [DecidableEq I] in
theorem pivotProd_apply_of_orth (b : I → V) (c : ℕ → I) (m : ℕ) {x : V}
    (h : ∀ k, 1 ≤ k → k ≤ m → β (b (c k)) x = 0) :
    (pivotProd hβ b c m : V →ₗ[ZMod 2] V) x = x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pivotProd_succ, Units.val_mul, Module.End.mul_apply,
      ih fun k hk1 hkm => h k hk1 (by omega)]
    exact transv_apply_of_orth hβ (h (m + 1) (by omega) le_rfl)

omit [DecidableEq I] in
theorem ofFn_prod_eq_pivotProd (b : I → V) (c : ℕ → I) (m : ℕ) :
    (List.ofFn fun k : Fin m => transv hβ (b (c (m - k)))).prod = pivotProd hβ b c m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, pivotProd_succ, ← ih]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ]
    congr 3
    funext k
    congr 3
    omega

@[expose] def cycAdj (n k l : ℕ) : Prop :=
  k + 1 = l ∨ l + 1 = k ∨ (k + 1 = n ∧ l = 0) ∨ (l + 1 = n ∧ k = 0)

instance (n k l : ℕ) : Decidable (cycAdj n k l) := by
  unfold cycAdj
  infer_instance

section Cycle

omit [DecidableEq I] in
theorem pivotProd_apply {n : ℕ} (b : I → V) (cn : ℕ → I)
    (hcyc : ∀ k l, k < n → l < n → β (b (cn k)) (b (cn l)) = if cycAdj n k l then 1 else 0)
    (m : ℕ) (hm : m + 2 ≤ n) :
    (pivotProd hβ b cn m : V →ₗ[ZMod 2] V) (b (cn 0)) = ∑ k ∈ Finset.range (m + 1), b (cn k) := by
  induction m with
  | zero => simp [pivotProd]
  | succ m ih =>
    rw [pivotProd_succ, Units.val_mul, Module.End.mul_apply, ih (by omega), transv_apply]
    have hpair : β (b (cn (m + 1))) (∑ k ∈ Finset.range (m + 1), b (cn k)) = 1 := by
      rw [map_sum, Finset.sum_eq_single m]
      · rw [hcyc _ _ (by omega) (by omega), ite_eq_left (by unfold cycAdj; omega)]
      · intro k hk hkm
        rw [Finset.mem_range] at hk
        rw [hcyc _ _ (by omega) (by omega), ite_eq_right (by unfold cycAdj; omega)]
      · intro h
        exact absurd (Finset.mem_range.2 (by omega)) h
    rw [hpair, one_smul]
    exact (Finset.sum_range_succ _ (m + 1)).symm

omit [DecidableEq I] in
theorem pair_sum_cycle {n : ℕ} (hn : 3 ≤ n) (b : I → V) (cn : ℕ → I)
    (hcyc : ∀ k l, k < n → l < n → β (b (cn k)) (b (cn l)) = if cycAdj n k l then 1 else 0)
    {j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n) :
    β (∑ k ∈ Finset.range (n - 1), b (cn k)) (b (cn j)) = if j = n - 2 then 1 else 0 := by
  rw [LinearMap.BilinForm.sum_left,
    Finset.sum_congr rfl fun k hk => hcyc k j (by rw [Finset.mem_range] at hk; omega) hjn,
    Finset.sum_boole]
  by_cases hj : j + 3 ≤ n
  · have hf : (Finset.range (n - 1)).filter (fun k => cycAdj n k j) = {j - 1, j + 1} := by
      ext k
      rw [Finset.mem_filter]
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_singleton, cycAdj]
      omega
    rw [hf, Finset.card_pair (by omega), ite_eq_right (by omega)]
    rfl
  · by_cases hj2 : j = n - 2
    · have hf : (Finset.range (n - 1)).filter (fun k => cycAdj n k j) = {n - 3} := by
        ext k
        rw [Finset.mem_filter]
        simp only [Finset.mem_range, Finset.mem_singleton, cycAdj]
        omega
      rw [hf, Finset.card_singleton, ite_eq_left hj2]
      rfl
    · have hf : (Finset.range (n - 1)).filter (fun k => cycAdj n k j) = {n - 2, 0} := by
        ext k
        rw [Finset.mem_filter]
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_singleton, cycAdj]
        omega
      rw [hf, Finset.card_pair (by omega), ite_eq_right hj2]
      rfl

end Cycle

theorem indexed_transvection_cycle_move [FiniteDimensional (ZMod 2) V] [Fintype I] [Nonempty I]
    (a : I → V) (ha0 : ∀ i, a i ≠ 0) :
    (∀ p q, p ≠ q →
      Submodule.span (ZMod 2) (Set.range (indexMove hβ a p q)) =
        Submodule.span (ZMod 2) (Set.range a) ∧
      Subgroup.closure (Set.range fun i => transv hβ (indexMove hβ a p q i)) =
        Subgroup.closure (Set.range fun i => transv hβ (a i)) ∧
      ((pairGraph hβ (indexMove hβ a p q)).Connected ↔ (pairGraph hβ a).Connected) ∧
      ∀ i, indexMove hβ a p q i ≠ 0) ∧
    ∀ (n : ℕ) (hn : 3 ≤ n) (c : Fin n → I), Function.Injective c →
      (∀ k l : Fin n, (pairGraph hβ a).Adj (c k) (c l) ↔ cycAdj n k l) →
      let P := (List.ofFn fun k : Fin (n - 2) => transv hβ (a (c ⟨n - 2 - k, by omega⟩))).prod
      let c₀ := c ⟨0, by omega⟩
      let a' := applyAt (insert c₀ (Finset.univ \ Finset.univ.image c)) P a
      Relation.ReflTransGen (IsIndexMove hβ) a a' ∧
      a' c₀ = ∑ k : Fin (n - 1), a (c (Fin.castLE (Nat.sub_le n 1) k)) ∧
      (∀ k : Fin n, (k : ℕ) ≠ 0 → (β (a' c₀) (a' (c k)) = 1 ↔ (k : ℕ) = n - 2)) ∧
      (∀ j, j ∉ Set.range c → β (a' c₀) (a' j) = β (a c₀) (a j)) ∧
      (pairGraph hβ a').degree c₀ + 1 = (pairGraph hβ a).degree c₀ ∧
      ∀ J : Finset I, (∀ k, c k ∈ J) →
        (∀ k : Fin n, 1 ≤ (k : ℕ) → (k : ℕ) ≤ n - 2 → ∀ j ∉ J, β (a (c k)) (a j) = 0) →
        let a'' := applyAt (insert c₀ (J \ Finset.univ.image c)) P a
        Relation.ReflTransGen (IsIndexMove hβ) a a'' ∧
        ∀ x y, (x ∉ J ∨ y ∉ J) → ((pairGraph hβ a'').Adj x y ↔ (pairGraph hβ a).Adj x y) := by
  refine ⟨fun p q hpq => ⟨span_indexMove hβ a hpq, closure_indexMove hβ a hpq,
    ⟨fun h => ?_, connected_indexMove hβ a hpq⟩, indexMove_ne_zero hβ a ha0 p q⟩, ?_⟩
  · have := connected_indexMove hβ (indexMove hβ a p q) hpq h
    rwa [indexMove_indexMove hβ hpq] at this
  intro n hn c hc hcyc P c₀ a'
  let cn : ℕ → I := fun k => if h : k < n then c ⟨k, h⟩ else c₀
  have hcn : ∀ k (hk : k < n), cn k = c ⟨k, hk⟩ := fun k hk => dite_eq_left hk
  have hcyc' : ∀ k l, k < n → l < n →
      β (a (cn k)) (a (cn l)) = if cycAdj n k l then 1 else 0 := by
    intro k l hk hl
    rw [hcn k hk, hcn l hl]
    have h := hcyc ⟨k, hk⟩ ⟨l, hl⟩
    rw [pairGraph_adj] at h
    split_ifs with h'
    · exact h.2 h'
    · exact zmod_two_eq_zero_of_ne_one fun h'' => h' (h.1 h'')
  have hP : P = pivotProd hβ a cn (n - 2) := by
    rw [← ofFn_prod_eq_pivotProd]
    change (List.ofFn fun k : Fin (n - 2) => transv hβ (a (c ⟨n - 2 - k, by omega⟩))).prod = _
    congr 2
    funext k
    rw [hcn _ (by omega)]
  have hPiso : ∀ x y, β ((P : V →ₗ[ZMod 2] V) x) ((P : V →ₗ[ZMod 2] V) y) = β x y := by
    rw [hP]
    exact pivotProd_mem_isometryGroup hβ a cn (n - 2)
  have hc0 : c₀ = cn 0 := (hcn 0 (by omega)).symm
  have hstart : (P : V →ₗ[ZMod 2] V) (a c₀) = ∑ k ∈ Finset.range (n - 1), a (cn k) := by
    rw [hP, hc0, pivotProd_apply hβ a cn hcyc' (n - 2) (by omega)]
    congr 1
    congr 1
    omega
  have hmemT : ∀ x, x ∈ Finset.univ.image c ↔ x ∈ Set.range c := fun x => by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
  have hck0 : ∀ k : Fin n, (k : ℕ) ≠ 0 → c k ≠ c₀ := fun k hk h => hk (by
    have := congrArg Fin.val (hc h)
    simpa using this)
  have hpiv : ∀ (S : Finset I), (∀ k : Fin n, (k : ℕ) ≠ 0 → c k ∉ S) →
      ∀ k, 1 ≤ k → k ≤ n - 2 → cn k ∉ S := fun S hS k hk1 hk2 => by
    rw [hcn k (by omega)]
    exact hS _ (by simp only; omega)
  have hS : ∀ k : Fin n, (k : ℕ) ≠ 0 → c k ∉ insert c₀ (Finset.univ \ Finset.univ.image c) := by
    intro k hk hmem
    rcases Finset.mem_insert.1 hmem with h | h
    · exact hck0 k hk h
    · exact (Finset.mem_sdiff.1 h).2 ((hmemT _).2 ⟨k, rfl⟩)
  have ha'c0 : a' c₀ = (P : V →ₗ[ZMod 2] V) (a c₀) := ite_eq_left (Finset.mem_insert_self _ _)
  have ha'ck : ∀ k : Fin n, (k : ℕ) ≠ 0 → a' (c k) = a (c k) := fun k hk =>
    ite_eq_right (hS k hk)
  have ha'j : ∀ j, j ∉ Set.range c → a' j = (P : V →ₗ[ZMod 2] V) (a j) := fun j hj =>
    ite_eq_left (Finset.mem_insert_of_mem (Finset.mem_sdiff.2 ⟨Finset.mem_univ _,
      fun h => hj ((hmemT j).1 h)⟩))
  have hB3 : ∀ k : Fin n, (k : ℕ) ≠ 0 → (β (a' c₀) (a' (c k)) = 1 ↔ (k : ℕ) = n - 2) := by
    intro k hk
    rw [ha'c0, ha'ck k hk, hstart, ← hcn k k.2,
      pair_sum_cycle hn a cn hcyc' (by omega) k.2]
    split_ifs with h
    · exact iff_of_true rfl h
    · exact iff_of_false (by decide) h
  have hB4 : ∀ j, j ∉ Set.range c → β (a' c₀) (a' j) = β (a c₀) (a j) := fun j hj => by
    rw [ha'c0, ha'j j hj, hPiso]
  refine ⟨?_, ?_, hB3, hB4, ?_, ?_⟩
  · show Relation.ReflTransGen (IsIndexMove hβ) a
      (applyAt (insert c₀ (Finset.univ \ Finset.univ.image c)) P a)
    rw [hP]
    exact rtg_applyAt_pivotProd hβ a cn _ (n - 2) (hpiv _ hS)
  · rw [ha'c0, hstart, ← Fin.sum_univ_eq_sum_range (fun k => a (cn k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcn k (by omega)]
    rfl
  · rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
      ← Finset.card_filter_add_card_filter_not (s := (pairGraph hβ a').neighborFinset c₀)
        (fun x => x ∈ Finset.univ.image c),
      ← Finset.card_filter_add_card_filter_not (s := (pairGraph hβ a).neighborFinset c₀)
        (fun x => x ∈ Finset.univ.image c)]
    have h1 : ((pairGraph hβ a').neighborFinset c₀).filter (fun x => x ∈ Finset.univ.image c) =
        {c ⟨n - 2, by omega⟩} := by
      ext x
      rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset, hmemT, Finset.mem_singleton]
      constructor
      · rintro ⟨hadj, k, rfl⟩
        have hk : (k : ℕ) ≠ 0 := by
          intro hk0
          have hk' : k = ⟨0, by omega⟩ := Fin.ext hk0
          rw [hk'] at hadj
          exact SimpleGraph.irrefl _ hadj
        rw [pairGraph_adj, hB3 k hk] at hadj
        exact congrArg c (Fin.ext hadj)
      · rintro rfl
        refine ⟨?_, ⟨_, rfl⟩⟩
        rw [pairGraph_adj, hB3 _ (by simp only; omega)]
    have h2 : ((pairGraph hβ a).neighborFinset c₀).filter (fun x => x ∈ Finset.univ.image c) =
        {c ⟨1, by omega⟩, c ⟨n - 1, by omega⟩} := by
      ext x
      rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset, hmemT, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hadj, k, rfl⟩
        have h := (hcyc ⟨0, by omega⟩ k).1 hadj
        unfold cycAdj at h
        simp only at h
        rcases (show (k : ℕ) = 1 ∨ (k : ℕ) = n - 1 by omega) with h' | h'
        · exact Or.inl (congrArg c (Fin.ext h'))
        · exact Or.inr (congrArg c (Fin.ext h'))
      · rintro (rfl | rfl)
        · exact ⟨(hcyc ⟨0, by omega⟩ ⟨1, by omega⟩).2 (show cycAdj n 0 1 by unfold cycAdj; omega),
            ⟨_, rfl⟩⟩
        · exact ⟨(hcyc ⟨0, by omega⟩ ⟨n - 1, by omega⟩).2
            (show cycAdj n 0 (n - 1) by unfold cycAdj; omega), ⟨_, rfl⟩⟩
    have h3 : ((pairGraph hβ a').neighborFinset c₀).filter (fun x => x ∉ Finset.univ.image c) =
        ((pairGraph hβ a).neighborFinset c₀).filter (fun x => x ∉ Finset.univ.image c) := by
      ext x
      rw [Finset.mem_filter, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset, hmemT]
      constructor
      · rintro ⟨hadj, hx⟩
        refine ⟨?_, hx⟩
        rw [pairGraph_adj, ← hB4 x hx]
        exact hadj
      · rintro ⟨hadj, hx⟩
        refine ⟨?_, hx⟩
        rw [pairGraph_adj, hB4 x hx]
        exact hadj
    have hne : c ⟨1, by omega⟩ ≠ c ⟨n - 1, by omega⟩ := fun h => by
      have h' := congrArg Fin.val (hc h)
      simp only at h'
      omega
    rw [h1, h2, h3, Finset.card_singleton, Finset.card_pair hne]
    omega
  · intro J hJ hpivJ a''
    have hc0J : c₀ ∈ J := hJ _
    have hS' : ∀ k : Fin n, (k : ℕ) ≠ 0 → c k ∉ insert c₀ (J \ Finset.univ.image c) := by
      intro k hk hmem
      rcases Finset.mem_insert.1 hmem with h | h
      · exact hck0 k hk h
      · exact (Finset.mem_sdiff.1 h).2 ((hmemT _).2 ⟨k, rfl⟩)
    have hPfix : ∀ j, j ∉ J → (P : V →ₗ[ZMod 2] V) (a j) = a j := by
      intro j hj
      rw [hP]
      refine pivotProd_apply_of_orth hβ a cn (n - 2) fun k hk1 hk2 => ?_
      rw [hcn k (by omega)]
      exact hpivJ ⟨k, by omega⟩ hk1 hk2 j hj
    have hout : ∀ j, j ∉ J → a'' j = a j := fun j hj => ite_eq_right fun h => by
      rcases Finset.mem_insert.1 h with h' | h'
      · rw [h'] at hj
        exact hj hc0J
      · exact hj (Finset.mem_sdiff.1 h').1
    have hmain : ∀ x y, x ∉ J → ((pairGraph hβ a'').Adj x y ↔ (pairGraph hβ a).Adj x y) := by
      intro x y hx
      rw [pairGraph_adj, pairGraph_adj, hout x hx]
      by_cases hy : y ∈ insert c₀ (J \ Finset.univ.image c)
      · have hya : a'' y = (P : V →ₗ[ZMod 2] V) (a y) := ite_eq_left hy
        have h1 := hPiso (a x) (a y)
        rw [hPfix x hx] at h1
        rw [hya, h1]
      · rw [show a'' y = a y from ite_eq_right hy]
    refine ⟨?_, fun x y hxy => ?_⟩
    · show Relation.ReflTransGen (IsIndexMove hβ) a
        (applyAt (insert c₀ (J \ Finset.univ.image c)) P a)
      rw [hP]
      exact rtg_applyAt_pivotProd hβ a cn _ (n - 2) (hpiv _ hS')
    · rcases hxy with hx | hy
      · exact hmain x y hx
      · rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (pairGraph hβ a)]
        exact hmain y x hy

end CFSG.Quasithin.SteinbergBN

module

public import CFSG.Sporadic.Th.Max3.MaxCheckInputs

public section

namespace CFSG.Sporadic.Th

open Native

section Words

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

@[expose] noncomputable def wordElt (u₁ u₂ : G) (w : List ℕ) : G := (w.map (lettersG u₁ u₂)).prod

theorem rep_wordTable (hn : n < 2 ^ 32) {P₁ P₂ : Table} {u₁ u₂ : G} (h₁ : Rep n P₁ u₁)
    (h₂ : Rep n P₂ u₂) (w : List ℕ) : Rep n (abTable n P₁ P₂ w) (wordElt u₁ u₂ w) := by
  induction w with
  | nil => exact Rep.idT hn
  | cons i w ih =>
    unfold abTable wordElt
    rw [List.foldr_cons, List.map_cons, List.prod_cons]
    exact Rep.compT (Rep.letters h₁ h₂ i) ih

theorem wordElt_mem (K : Subgroup G) {u₁ u₂ : G} (h₁ : u₁ ∈ K) (h₂ : u₂ ∈ K) (w : List ℕ) :
    wordElt u₁ u₂ w ∈ K := by
  unfold wordElt
  apply K.list_prod_mem
  intro g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact lettersG_mem K h₁ h₂ i

end Words

section HElt

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

@[expose] noncomputable def hElt (t : Array (ℕ × ℕ)) (r g₁ g₂ : G) (k : ℕ) : G :=
  if _h : 0 < (t[k]!).1 ∧ (t[k]!).1 - 1 < k then
    lettersG g₁ g₂ (t[k]!).2 * hElt t r g₁ g₂ ((t[k]!).1 - 1) * (lettersG g₁ g₂ (t[k]!).2)⁻¹
  else r
termination_by k

theorem hEval_eq (t : Array (ℕ × ℕ)) {R X Y Xi Yi : Table} {r g₁ g₂ : G} (hR : Rep n R r)
    (hX : Rep n X g₁) (hY : Rep n Y g₂) (hXi : Rep n Xi g₁⁻¹) (hYi : Rep n Yi g₂⁻¹) (k : ℕ) :
    ∀ q < n, hEval t R X Y Xi Yi k q = idx n (hElt t r g₁ g₂ k) q := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro q hq
    rw [Native.hEval.eq_def, hElt.eq_def]
    split_ifs with hk
    · have hl := Rep.letters hX hY (t[k]!).2
      have hli : Rep n (letters Xi Yi (t[k]!).2) (lettersG g₁ g₂ (t[k]!).2)⁻¹ := by
        have := Rep.letters hXi hYi (t[k]!).2
        unfold lettersG at this ⊢
        split_ifs at this ⊢ <;> exact this
      have hq' : ap (letters Xi Yi (t[k]!).2) q < n := by rw [hli q hq]; exact idx_lt _ hq
      rw [ih _ hk.2 _ hq', hli q hq, hl _ (idx_lt _ (idx_lt _ hq)), idx_mul, idx_mul]
    · exact hR q hq

theorem hElt_mem (K : Subgroup G) (t : Array (ℕ × ℕ)) {r g₁ g₂ : G} (hr : r ∈ K) (h₁ : g₁ ∈ K)
    (h₂ : g₂ ∈ K) (k : ℕ) : hElt t r g₁ g₂ k ∈ K := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [hElt.eq_def]
    split_ifs with hk
    · have hl := lettersG_mem K h₁ h₂ (t[k]!).2
      exact K.mul_mem (K.mul_mem hl (ih _ hk.2)) (K.inv_mem hl)
    · exact hr

theorem isConj_hElt (t : Array (ℕ × ℕ)) (r g₁ g₂ : G) (k : ℕ) : IsConj r (hElt t r g₁ g₂ k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [hElt.eq_def]
    split_ifs with hk
    · exact (ih _ hk.2).trans (isConj_iff.2 ⟨_, rfl⟩)
    · exact IsConj.refl r

@[expose] noncomputable def hElt2 (t₀ t₁ : Array (ℕ × ℕ)) (r₀ r₁ g₁ g₂ : G) (k : ℕ) : G :=
  if k < t₀.size then hElt t₀ r₀ g₁ g₂ k else hElt t₁ r₁ g₁ g₂ (k - t₀.size)

theorem hFp2_eq (hn2 : 2 < n) (t₀ t₁ : Array (ℕ × ℕ)) {R₀ R₁ X Y Xi Yi : Table} {r₀ r₁ g₁ g₂ : G}
    (hR₀ : Rep n R₀ r₀) (hR₁ : Rep n R₁ r₁) (hX : Rep n X g₁) (hY : Rep n Y g₂)
    (hXi : Rep n Xi g₁⁻¹) (hYi : Rep n Yi g₂⁻¹) (k : ℕ) :
    hFp2 t₀ t₁ R₀ R₁ X Y Xi Yi k =
      idx n (hElt2 t₀ t₁ r₀ r₁ g₁ g₂ k) 1 * 4294967296 + idx n (hElt2 t₀ t₁ r₀ r₁ g₁ g₂ k) 2 := by
  unfold hFp2 hElt2 hFp
  split_ifs
  · rw [hEval_eq t₀ hR₀ hX hY hXi hYi k 1 (by omega), hEval_eq t₀ hR₀ hX hY hXi hYi k 2 hn2]
  · rw [hEval_eq t₁ hR₁ hX hY hXi hYi _ 1 (by omega), hEval_eq t₁ hR₁ hX hY hXi hYi _ 2 hn2]

end HElt

theorem lt_of_adjacent_lt {f : ℕ → ℕ} {π : Array ℕ}
    (h : ∀ i, 1 ≤ i → i < π.size → f π[i - 1]! < f π[i]!) :
    ∀ i j, i < j → j < π.size → f π[i]! < f π[j]! := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    have hstep := h (j + 1) (by omega) hj
    simp only [Nat.add_sub_cancel] at hstep
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | heq
    · exact (ih hlt (by omega)).trans hstep
    · rw [heq]; exact hstep

theorem countFixAux_eq (T : Table) (k c : ℕ) :
    countFixAux T k c = c + ((Finset.range k).filter fun i => ap T i = i).card := by
  induction k generalizing c with
  | zero => simp [countFixAux]
  | succ k ih =>
    rw [countFixAux, ih, Finset.range_add_one, Finset.filter_insert]
    have hk : k ∉ (Finset.range k).filter fun i => ap T i = i := by simp
    by_cases h : ap T k = k
    · simp [h, Finset.card_insert_of_notMem hk]
      ring
    · simp [h]

theorem countFix_eq (n : ℕ) (T : Table) :
    countFix n T = ((Finset.range n).filter fun i => ap T i = i).card := by
  rw [countFix, countFixAux_eq, zero_add]

theorem card_fix_eq_countFix {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)] {T : Table}
    {g : G} (hT : Rep n T g) : Nat.card {p : Fin n // g • p = p} = countFix n T := by
  classical
  rw [countFix_eq]
  have e : {p : Fin n // g • p = p} ≃ ((Finset.range n).filter fun i => ap T i = i) :=
    { toFun := fun p => ⟨p.1.val, by
          rw [Finset.mem_filter, Finset.mem_range, hT _ p.1.isLt, idx_of_lt g p.1.isLt]
          exact ⟨p.1.isLt, congrArg Fin.val p.2⟩⟩
      invFun := fun i => ⟨⟨i.1, Finset.mem_range.1 (Finset.mem_filter.1 i.2).1⟩, by
          have h := (Finset.mem_filter.1 i.2)
          apply Fin.ext
          rw [← idx_of_lt g (Finset.mem_range.1 h.1), ← hT _ (Finset.mem_range.1 h.1)]
          exact h.2⟩
      left_inv := fun p => rfl
      right_inv := fun i => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

@[expose] noncomputable def hRoot0 : J := wordElt xJ yJ hRootWord0

@[expose] noncomputable def hRoot1 :
    J := wordElt xJ yJ hRootWord1 ^ 9

section Facts

variable {c₀ : ℕ} (hC : CertFacts c₀)

include hC

theorem orderOf_eq_two_of_table
    {T : Table} {g : J} (hT : Rep nX T g)
    (h2 : compT nX T T = idT nX) (h1 : ap T 1 ≠ 1) : orderOf g = 2 := by
  have hn := nX_lt hC
  have hsq : g * g = 1 := by
    apply eq_one_of_idx_id hC
    intro i hi
    have h := Rep.compT hT hT i hi
    rw [h2, Rep.idT (G := J) hn i hi, idx_one] at h
    exact h.symm
  have hne : g ≠ 1 := by
    rintro rfl
    have h1' := hT 1 (by rw [hC.count]; norm_num)
    rw [idx_one] at h1'
    exact h1 h1'
  exact orderOf_eq_prime (by rw [sq]; exact hsq) hne

end Facts

end CFSG.Sporadic.Th

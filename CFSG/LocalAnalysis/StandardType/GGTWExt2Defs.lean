module

public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTWPosCoxK (k c m : ℕ) : Prop :=
  ((c = 0 ∨ c + 1 = k) ∧ (m = 3 ∨ m = 4)) ∨ (3 ≤ k ∧ (c = 1 ∨ c + 2 = k) ∧ m = 3) ∨
    (5 ≤ k ∧ k ≤ 7 ∧ (c = 2 ∨ c + 3 = k) ∧ m = 3)

instance (k c m : ℕ) : Decidable (GGTWPosCoxK k c m) := by
  unfold GGTWPosCoxK; infer_instance

@[expose] def GGTWPosCox (N : ℕ) (pos : GGTWPos) (c m : ℕ) : Prop :=
  GGTWPosCoxK (N - 3) (ggTWPlace pos c) m

@[expose] def GGTWChain {n k : ℕ} (X : CoxeterMatrix (Fin n)) (f : Fin k → Fin n) : Prop :=
  ∀ i j, X (f i) (f j) = CoxeterMatrix.A k i j

@[expose] def GGTWExt2Fin {n k : ℕ} (X : CoxeterMatrix (Fin n)) (f : Fin k → Fin n)
    (t t' : Fin n) : Prop :=
  (∃ c0 : Fin k, GGTWPosCoxK k c0.val (X t (f c0)) ∧ ∀ j, j ≠ c0 → X t (f j) = 2) ∨
    ((∀ j, X t (f j) = 2) ∧ ∃ c0 : Fin k, GGTWPosCoxK k c0.val (X t' (f c0)) ∧
      (∀ j, j ≠ c0 → X t' (f j) = 2) ∧
      (X t t' = 3 ∨ (X t t' = 4 ∧ X t' (f c0) = 3 ∧ (c0.val = 0 ∨ c0.val + 1 = k))))

instance {n k : ℕ} (X : CoxeterMatrix (Fin n)) (f : Fin k → Fin n) (t t' : Fin n) :
    Decidable (GGTWExt2Fin X f t t') := by
  unfold GGTWExt2Fin; infer_instance

@[expose] def GGTWExt2All {n : ℕ} (X : CoxeterMatrix (Fin n)) : Prop :=
  ∀ (f : Fin (n - 2) → Fin n) (t t' : Fin n), GGTWChain X f → (∀ i, t ≠ f i) →
    (∀ i, t' ≠ f i) → t ≠ t' → GGTWExt2Fin X f t t'

@[expose] def ggTWChainsF {n : ℕ} (X : CoxeterMatrix (Fin n)) : (k : ℕ) → List (Fin k → Fin n)
  | 0 => [Fin.elim0]
  | k + 1 => (ggTWChainsF X k).flatMap fun g => (List.finRange n).filterMap fun v =>
      if ∀ i : Fin k, X (g i) v = if i.val + 1 = k then 3 else 2 then
        some (Fin.snoc (α := fun _ => Fin n) g v) else none

private lemma ggTW_A_succ_castSucc {k : ℕ} (i j : Fin k) :
    CoxeterMatrix.A (k + 1) i.castSucc j.castSucc = CoxeterMatrix.A k i j := by
  unfold CoxeterMatrix.A
  simp only [Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · have hne : i.castSucc ≠ j.castSucc := fun h => hij (Fin.castSucc_injective k h)
    rw [if_neg hne, if_neg hij]
    have hc : ((j.castSucc : Fin (k + 1)).val + 1 = (i.castSucc : Fin (k + 1)).val ∨
        (i.castSucc : Fin (k + 1)).val + 1 = (j.castSucc : Fin (k + 1)).val) ↔
        (j.val + 1 = i.val ∨ i.val + 1 = j.val) := by
      simp [Fin.val_castSucc]
    by_cases h : j.val + 1 = i.val ∨ i.val + 1 = j.val
    · rw [if_pos (hc.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

private lemma ggTW_A_last {k : ℕ} (i : Fin k) :
    CoxeterMatrix.A (k + 1) i.castSucc (Fin.last k) =
      if i.val + 1 = k then 3 else 2 := by
  unfold CoxeterMatrix.A
  simp only [Matrix.of_apply]
  have hne : i.castSucc ≠ Fin.last k := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_castSucc, Fin.val_last] at this
    omega
  rw [if_neg hne]
  have hc : ((Fin.last k : Fin (k + 1)).val + 1 = (i.castSucc : Fin (k + 1)).val ∨
      (i.castSucc : Fin (k + 1)).val + 1 = (Fin.last k : Fin (k + 1)).val) ↔
      i.val + 1 = k := by
    simp [Fin.val_castSucc, Fin.val_last]
    omega
  by_cases h : i.val + 1 = k
  · rw [if_pos (hc.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

theorem ggTWChain_mem_chainsF {n k : ℕ} {X : CoxeterMatrix (Fin n)} {f : Fin k → Fin n}
    (hf : GGTWChain X f) : f ∈ ggTWChainsF X k := by
  induction k with
  | zero =>
    have hf0 : f = Fin.elim0 := by funext i; exact i.elim0
    subst hf0
    simp [ggTWChainsF]
  | succ k ih =>
    let g : Fin k → Fin n := fun i => f i.castSucc
    let v : Fin n := f (Fin.last k)
    have hg : GGTWChain X g := by
      intro i j
      have h := hf i.castSucc j.castSucc
      rw [ggTW_A_succ_castSucc] at h
      exact h
    have hv : ∀ i : Fin k, X (g i) v = if i.val + 1 = k then 3 else 2 := by
      intro i
      have h := hf i.castSucc (Fin.last k)
      rw [ggTW_A_last] at h
      exact h
    rw [ggTWChainsF, List.mem_flatMap]
    refine ⟨g, ih hg, ?_⟩
    rw [List.mem_filterMap]
    refine ⟨v, List.mem_finRange v, ?_⟩
    rw [if_pos hv]
    have hginit : g = Fin.init f := rfl
    rw [hginit]
    exact congrArg some (Fin.snoc_init_self f)

theorem ggTWExt2All_of_check {n : ℕ} {X : CoxeterMatrix (Fin n)}
    (h : (ggTWChainsF X (n - 2)).all (fun g => decide (∀ t t' : Fin n, (∀ i, t ≠ g i) →
      (∀ i, t' ≠ g i) → t ≠ t' → GGTWExt2Fin X g t t')) = true) : GGTWExt2All X := by
  intro f t t' hf ht ht' htt'
  have hmem := List.all_eq_true.mp h f (ggTWChain_mem_chainsF hf)
  exact of_decide_eq_true hmem t t' ht ht' htt'

@[expose] def GGTWExt2Cox (N : ℕ) (pos : GGTWPos) {Λa : Type}
    (M : CoxeterMatrix ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa)) (a : Λa) : Prop :=
  (∃ c0 : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      GGTWPosCox N pos c0.1.val (M (Sum.inr a) (Sum.inl c0)) ∧
        ∀ j, j ≠ c0 → M (Sum.inr a) (Sum.inl j) = 2) ∨
    ((∀ j, M (Sum.inr a) (Sum.inl j) = 2) ∧
      ∃ (b : Λa) (c0 : {c : Fin (N - 1) // ggTWInJ N pos c.val}), b ≠ a ∧
        GGTWPosCox N pos c0.1.val (M (Sum.inr b) (Sum.inl c0)) ∧
        (∀ j, j ≠ c0 → M (Sum.inr b) (Sum.inl j) = 2) ∧
        (M (Sum.inr a) (Sum.inr b) = 3 ∨
          (M (Sum.inr a) (Sum.inr b) = 4 ∧ M (Sum.inr b) (Sum.inl c0) = 3 ∧
            (ggTWPlace pos c0.1.val = 0 ∨ ggTWPlace pos c0.1.val + 1 = N - 3))))

private lemma ggTW_A_shift {n m : ℕ} (off : ℕ) (i j : Fin m)
    (hi : i.val + off < n) (hj : j.val + off < n) :
    CoxeterMatrix.A n ⟨i.val + off, hi⟩ ⟨j.val + off, hj⟩ = CoxeterMatrix.A m i j := by
  unfold CoxeterMatrix.A
  simp only [Matrix.of_apply, Fin.mk.injEq]
  by_cases hij : i = j
  · subst hij
    simp
  · have hne : i.val + off ≠ j.val + off := by omega
    rw [if_neg hne, if_neg hij]
    have hc : ((j.val + off) + 1 = i.val + off ∨ (i.val + off) + 1 = j.val + off) ↔
        (j.val + 1 = i.val ∨ i.val + 1 = j.val) := by omega
    by_cases h : j.val + 1 = i.val ∨ i.val + 1 = j.val
    · rw [if_pos (hc.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

private lemma ggTWExt2Cox_transfer {N : ℕ} (pos : GGTWPos) {Λa : Type}
    (hΛa : Nat.card Λa = 2) {X : CoxeterMatrix (Fin (N - 1))} (hX : GGTWExt2All X)
    {M : CoxeterMatrix ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa)}
    (e : Fin (N - 1) ≃ ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa))
    (hM : M = X.reindex e)
    (hJ : ∀ i j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      M (Sum.inl i) (Sum.inl j) = CoxeterMatrix.A (N - 1) i.1 j.1)
    (a : Λa)
    (Φ : {c : Fin (N - 1) // ggTWInJ N pos c.val} → Fin (N - 1 - 2))
    (σ : Fin (N - 1 - 2) → {c : Fin (N - 1) // ggTWInJ N pos c.val})
    (hΦσ : ∀ k, Φ (σ k) = k)
    (hσΦ : ∀ j, σ (Φ j) = j)
    (hplace : ∀ k, ggTWPlace pos (σ k).1.val = k.val)
    (hA : ∀ k l, CoxeterMatrix.A (N - 1) (σ k).1 (σ l).1 =
      CoxeterMatrix.A (N - 1 - 2) k l) :
    GGTWExt2Cox N pos M a := by
  obtain ⟨b, hbne, -⟩ := (Nat.card_eq_two_iff' a).mp hΛa
  let t : Fin (N - 1) := e.symm (Sum.inr a)
  let t' : Fin (N - 1) := e.symm (Sum.inr b)
  let f : Fin (N - 1 - 2) → Fin (N - 1) := fun k => e.symm (Sum.inl (σ k))
  have hf : GGTWChain X f := by
    intro k l
    have h := hJ (σ k) (σ l)
    rw [hM, CoxeterMatrix.reindex_apply] at h
    have h' : X (f k) (f l) = CoxeterMatrix.A (N - 1) (σ k).1 (σ l).1 := h
    rw [h']
    exact hA k l
  have ht : ∀ k, t ≠ f k := by
    intro k h
    exact Sum.inr_ne_inl (e.symm.injective h)
  have ht' : ∀ k, t' ≠ f k := by
    intro k h
    exact Sum.inr_ne_inl (e.symm.injective h)
  have htt' : t ≠ t' := by
    intro h
    have hab : a = b := Sum.inr.inj (e.symm.injective h)
    exact hbne hab.symm
  have hM_a : ∀ c : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      M (Sum.inr a) (Sum.inl c) = X t (f (Φ c)) := by
    intro c
    rw [hM, CoxeterMatrix.reindex_apply]
    conv_lhs => rw [← hσΦ c]
  have hM_b : ∀ c : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      M (Sum.inr b) (Sum.inl c) = X t' (f (Φ c)) := by
    intro c
    rw [hM, CoxeterMatrix.reindex_apply]
    conv_lhs => rw [← hσΦ c]
  have hM_tt' : M (Sum.inr a) (Sum.inr b) = X t t' := by
    rw [hM, CoxeterMatrix.reindex_apply]
  have h := hX f t t' hf ht ht' htt'
  unfold GGTWExt2Fin at h
  unfold GGTWExt2Cox
  rcases h with ⟨c0, hpos, hall⟩ | ⟨hall_a, c0, hpos, hall_b, hlast⟩
  · refine Or.inl ⟨σ c0, ?_, ?_⟩
    · show GGTWPosCoxK (N - 3) (ggTWPlace pos (σ c0).1.val) (M (Sum.inr a) (Sum.inl (σ c0)))
      rw [hplace c0, show N - 3 = N - 1 - 2 by omega, hM_a (σ c0), hΦσ c0]
      exact hpos
    · intro j hj
      rw [hM_a j]
      exact hall (Φ j) (fun h' => hj (by rw [← hσΦ j, h']))
  · refine Or.inr ⟨?_, b, σ c0, hbne, ?_, ?_, ?_⟩
    · intro j
      rw [hM_a j]
      exact hall_a (Φ j)
    · show GGTWPosCoxK (N - 3) (ggTWPlace pos (σ c0).1.val) (M (Sum.inr b) (Sum.inl (σ c0)))
      rw [hplace c0, show N - 3 = N - 1 - 2 by omega, hM_b (σ c0), hΦσ c0]
      exact hpos
    · intro j hj
      rw [hM_b j]
      exact hall_b (Φ j) (fun h' => hj (by rw [← hσΦ j, h']))
    · rw [hM_tt', hM_b (σ c0), hΦσ c0, hplace c0,
        show N - 3 = N - 1 - 2 by omega]
      rcases hlast with h3 | ⟨h4, hb3, hend⟩
      · exact Or.inl h3
      · exact Or.inr ⟨h4, hb3, hend⟩

theorem ggTWExt2Cox_of_all {N : ℕ} (hN : 5 ≤ N) (pos : GGTWPos) {Λa : Type}
    (hΛa : Nat.card Λa = 2) {X : CoxeterMatrix (Fin (N - 1))} (hX : GGTWExt2All X)
    {M : CoxeterMatrix ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa)}
    (e : Fin (N - 1) ≃ ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa)) (hM : M = X.reindex e)
    (hJ : ∀ i j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      M (Sum.inl i) (Sum.inl j) = CoxeterMatrix.A (N - 1) i.1 j.1) (a : Λa) :
    GGTWExt2Cox N pos M a := by
  cases pos with
  | ends =>
    let Φ : {c : Fin (N - 1) // ggTWInJ N GGTWPos.ends c.val} → Fin (N - 1 - 2) :=
      fun c => ⟨c.1.val - 1, by
        have h1 := c.2.1
        have h2 := c.2.2
        omega⟩
    let σ : Fin (N - 1 - 2) → {c : Fin (N - 1) // ggTWInJ N GGTWPos.ends c.val} :=
      fun k => ⟨⟨k.val + 1, by omega⟩, by
        simp only [ggTWInJ]
        constructor <;> omega⟩
    have hΦσ : ∀ k, Φ (σ k) = k := by
      intro k
      apply Fin.ext
      show (k.val + 1) - 1 = k.val
      omega
    have hσΦ : ∀ j, σ (Φ j) = j := by
      intro j
      apply Subtype.ext
      apply Fin.ext
      show (j.1.val - 1) + 1 = j.1.val
      have hj : 1 ≤ j.1.val := j.2.1
      omega
    have hplace : ∀ k, ggTWPlace GGTWPos.ends (σ k).1.val = k.val := by
      intro k
      show (k.val + 1) - 1 = k.val
      omega
    have hA : ∀ k l, CoxeterMatrix.A (N - 1) (σ k).1 (σ l).1 =
        CoxeterMatrix.A (N - 1 - 2) k l := by
      intro k l
      dsimp only [σ]
      exact ggTW_A_shift (n := N - 1) (m := N - 1 - 2) 1 k l (by omega) (by omega)
    exact ggTWExt2Cox_transfer GGTWPos.ends hΛa hX e hM hJ a Φ σ hΦσ hσΦ hplace hA
  | adj =>
    let Φ : {c : Fin (N - 1) // ggTWInJ N GGTWPos.adj c.val} → Fin (N - 1 - 2) :=
      fun c => ⟨c.1.val, by
        have h : c.1.val + 4 ≤ N := c.2
        omega⟩
    let σ : Fin (N - 1 - 2) → {c : Fin (N - 1) // ggTWInJ N GGTWPos.adj c.val} :=
      fun k => ⟨⟨k.val, by omega⟩, by
        simp only [ggTWInJ]
        omega⟩
    have hΦσ : ∀ k, Φ (σ k) = k := by
      intro k
      apply Fin.ext
      show k.val = k.val
      rfl
    have hσΦ : ∀ j, σ (Φ j) = j := by
      intro j
      apply Subtype.ext
      apply Fin.ext
      show j.1.val = j.1.val
      rfl
    have hplace : ∀ k, ggTWPlace GGTWPos.adj (σ k).1.val = k.val := by
      intro k
      show k.val = k.val
      rfl
    have hA : ∀ k l, CoxeterMatrix.A (N - 1) (σ k).1 (σ l).1 =
        CoxeterMatrix.A (N - 1 - 2) k l := by
      intro k l
      dsimp only [σ]
      simpa using ggTW_A_shift (n := N - 1) (m := N - 1 - 2) 0 k l (by omega) (by omega)
    exact ggTWExt2Cox_transfer GGTWPos.adj hΛa hX e hM hJ a Φ σ hΦσ hσΦ hplace hA

end CFSG.StandardType

end

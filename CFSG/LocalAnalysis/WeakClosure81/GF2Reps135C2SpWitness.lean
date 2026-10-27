module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBRealize

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.StandardType

@[expose] def spAct {n : ℕ} (π : Equiv.Perm (Fin n)) (s c : Fin n → ℤ) : Fin n → ℤ :=
  fun b => s (π.symm b) * c (π.symm b)

@[expose] def spFlip {n : ℕ} (s : Fin n → ℤ) : Equiv.Perm (Fin n ⊕ Fin n) where
  toFun x := if s (Sum.elim id id x) = 1 then x else x.swap
  invFun x := if s (Sum.elim id id x) = 1 then x else x.swap
  left_inv x := by rcases x with a | a <;> by_cases h : s a = 1 <;> simp [h]
  right_inv x := by rcases x with a | a <;> by_cases h : s a = 1 <;> simp [h]

@[expose] def spMonoPerm {n : ℕ} (π : Equiv.Perm (Fin n)) (s : Fin n → ℤ) :
    Equiv.Perm (Fin n ⊕ Fin n) :=
  (spFlip s).trans (Equiv.sumCongr π π)

theorem spMonoPerm_one (n : ℕ) :
    spMonoPerm (1 : Equiv.Perm (Fin n)) (1 : Fin n → ℤ) = 1 := by
  ext x
  rcases x with a | a <;> simp [spMonoPerm, spFlip]

theorem spMonoPerm_mul {n : ℕ} {π₁ π₂ : Equiv.Perm (Fin n)} {s₁ s₂ : Fin n → ℤ}
    (hs₁ : SpIsSign s₁) (hs₂ : SpIsSign s₂) :
    spMonoPerm (π₁ * π₂) (fun c => s₂ c * s₁ (π₂ c)) =
      spMonoPerm π₁ s₁ * spMonoPerm π₂ s₂ := by
  ext x
  rcases x with a | a <;>
    (rcases hs₂ a with h₂ | h₂ <;> rcases hs₁ (π₂ a) with h₁ | h₁ <;>
      simp [spMonoPerm, spFlip, h₂, h₁, Equiv.Perm.mul_apply])

theorem spMonoPerm_inl {n : ℕ} (π : Equiv.Perm (Fin n)) (s : Fin n → ℤ) (a : Fin n) :
    spMonoPerm π s (Sum.inl a) = if s a = 1 then Sum.inl (π a) else Sum.inr (π a) := by
  by_cases h : s a = 1 <;> simp [spMonoPerm, spFlip, h, Equiv.sumCongr]

theorem spMonoPerm_inr {n : ℕ} (π : Equiv.Perm (Fin n)) (s : Fin n → ℤ) (a : Fin n) :
    spMonoPerm π s (Sum.inr a) = if s a = 1 then Sum.inr (π a) else Sum.inl (π a) := by
  by_cases h : s a = 1 <;> simp [spMonoPerm, spFlip, h, Equiv.sumCongr]

theorem spMonoPerm_swap {n : ℕ} (π : Equiv.Perm (Fin n)) (s : Fin n → ℤ)
    (x : Fin n ⊕ Fin n) : spMonoPerm π s x.swap = (spMonoPerm π s x).swap := by
  rcases x with a | a <;> by_cases h : s a = 1 <;>
    simp [spMonoPerm, spFlip, h, Equiv.sumCongr_apply]

@[expose] def spTypeVec {n : ℕ} (S : Finset (Fin n)) : Fin n → ℤ :=
  fun a => ((S.filter (a ≤ ·)).card : ℤ)


private lemma spTypeVec_nonneg {n : ℕ} (S : Finset (Fin n)) (a : Fin n) :
    0 ≤ spTypeVec S a := by
  unfold spTypeVec
  positivity

private lemma spTypeVec_zero {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) :
    spTypeVec S ⟨0, hn⟩ = (S.card : ℤ) := by
  unfold spTypeVec
  rw [Finset.filter_true_of_mem (p := fun x => (⟨0, hn⟩ : Fin n) ≤ x) (fun x _ => by
    rw [Fin.le_iff_val_le_val]
    exact Nat.zero_le _)]

private lemma spTypeVec_anti {n : ℕ} (S : Finset (Fin n)) {a b : Fin n} (hab : a ≤ b) :
    spTypeVec S b ≤ spTypeVec S a := by
  unfold spTypeVec
  apply Int.ofNat_le.mpr
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, le_trans hab hx.2⟩

private lemma spTypeVec_succ {n : ℕ} (S : Finset (Fin n)) (a : Fin n) (ha : a.val + 1 < n) :
    spTypeVec S a =
      spTypeVec S ⟨a.val + 1, ha⟩ + (if a ∈ S then 1 else 0) := by
  unfold spTypeVec
  by_cases haS : a ∈ S
  · have hins : S.filter (a ≤ ·) =
        insert a (S.filter ((⟨a.val + 1, ha⟩ : Fin n) ≤ ·)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hxS, hax⟩
        rw [Fin.le_iff_val_le_val] at hax
        rcases eq_or_lt_of_le hax with h | h
        · left; exact Fin.ext h.symm
        · right; refine ⟨hxS, ?_⟩
          rw [Fin.le_iff_val_le_val]
          exact h
      · rintro (rfl | ⟨hxS, hax⟩)
        · exact ⟨haS, le_rfl⟩
        · refine ⟨hxS, ?_⟩
          rw [Fin.le_iff_val_le_val] at hax ⊢
          change a.val + 1 ≤ x.val at hax
          omega
    rw [hins, Finset.card_insert_of_notMem, if_pos haS]
    · push_cast; ring
    · intro hmem
      rw [Finset.mem_filter] at hmem
      have h : a.val + 1 ≤ a.val := hmem.2
      omega
  · have heq : S.filter (a ≤ ·) = S.filter ((⟨a.val + 1, ha⟩ : Fin n) ≤ ·) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hxS, hax⟩
        rw [Fin.le_iff_val_le_val] at hax
        refine ⟨hxS, ?_⟩
        rw [Fin.le_iff_val_le_val]
        have hne : x.val ≠ a.val := fun h => haS (Fin.ext h.symm ▸ hxS)
        change a.val + 1 ≤ x.val
        omega
      · rintro ⟨hxS, hax⟩
        refine ⟨hxS, ?_⟩
        rw [Fin.le_iff_val_le_val] at hax ⊢
        change a.val + 1 ≤ x.val at hax
        omega
    rw [heq, if_neg haS]
    simp

private lemma spTypeVec_one_pos {n : ℕ} (hn : 3 ≤ n) {S : Finset (Fin n)} (hS : S.Nonempty)
    (hS0 : S ≠ {⟨0, by omega⟩}) :
    1 ≤ spTypeVec S ⟨1, by omega⟩ := by
  by_contra hlt
  have hnon := spTypeVec_nonneg S ⟨1, by omega⟩
  have hz : spTypeVec S ⟨1, by omega⟩ = 0 := by omega
  have hcard : (S.filter (fun x => (⟨1, by omega⟩ : Fin n) ≤ x)).card = 0 := by
    unfold spTypeVec at hz
    exact_mod_cast hz
  have hempty := Finset.card_eq_zero.mp hcard
  have hsub : S ⊆ {⟨0, by omega⟩} := by
    intro x hx
    rw [Finset.mem_singleton]
    by_contra hx0
    have hxmem : x ∈ S.filter (fun y => (⟨1, by omega⟩ : Fin n) ≤ y) := by
      rw [Finset.mem_filter]
      refine ⟨hx, ?_⟩
      rw [Fin.le_iff_val_le_val]
      change 1 ≤ x.val
      have : x.val ≠ 0 := fun h => hx0 (Fin.ext h)
      omega
    rw [hempty] at hxmem
    exact Finset.notMem_empty x hxmem
  have h0mem : (⟨0, by omega⟩ : Fin n) ∈ S := by
    obtain ⟨x, hx⟩ := hS
    have hxeq : x = ⟨0, by omega⟩ := by simpa using hsub hx
    simpa [hxeq] using hx
  apply hS0
  ext y
  rw [Finset.mem_singleton]
  constructor
  · intro hy; simpa using hsub hy
  · intro hy; rw [hy]; exact h0mem

private lemma spAct_ne_of_neg {n : ℕ} (hn : 0 < n) {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    (hπ : π ⟨0, by omega⟩ = ⟨0, by omega⟩) (hs : s ⟨0, by omega⟩ = -1)
    {v w : Fin n → ℤ} (hv : 0 < v ⟨0, by omega⟩) (hw : 0 < w ⟨0, by omega⟩) :
    v ≠ spAct π s w := by
  intro h
  have h0 := congrFun h ⟨0, by omega⟩
  have hπ0 : π.symm ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
    simpa [hπ] using Equiv.symm_apply_apply π (⟨0, by omega⟩ : Fin n)
  have hneg : spAct π s w ⟨0, by omega⟩ = -w ⟨0, by omega⟩ := by
    simp [spAct, hπ0, hs]
  rw [hneg] at h0
  omega

private lemma spAct_ne_of_sum {n : ℕ} (hn : 2 ≤ n) {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    (hπ0 : π ⟨0, by omega⟩ = ⟨1, by omega⟩)
    (hπ1 : π ⟨1, by omega⟩ = ⟨0, by omega⟩)
    (hs0 : s ⟨0, by omega⟩ = -1) (hs1 : s ⟨1, by omega⟩ = -1)
    {v w : Fin n → ℤ}
    (hv : 0 < v ⟨0, by omega⟩ + v ⟨1, by omega⟩)
    (hw : 0 < w ⟨0, by omega⟩ + w ⟨1, by omega⟩) :
    v ≠ spAct π s w := by
  intro h
  have h0 := congrFun h ⟨0, by omega⟩
  have h1 := congrFun h ⟨1, by omega⟩
  have hs0' : π.symm ⟨0, by omega⟩ = ⟨1, by omega⟩ := by
    simpa [hπ1] using Equiv.symm_apply_apply π (⟨1, by omega⟩ : Fin n)
  have hs1' : π.symm ⟨1, by omega⟩ = ⟨0, by omega⟩ := by
    simpa [hπ0] using Equiv.symm_apply_apply π (⟨0, by omega⟩ : Fin n)
  have e0 : spAct π s w ⟨0, by omega⟩ = -w ⟨1, by omega⟩ := by
    simp [spAct, hs0', hs1]
  have e1 : spAct π s w ⟨1, by omega⟩ = -w ⟨0, by omega⟩ := by
    simp [spAct, hs1', hs0]
  rw [e0] at h0
  rw [e1] at h1
  omega

private lemma spWitness_neg_zero {n : ℕ} (hn : 3 ≤ n) {c : Fin n → ℤ}
    (h0 : 0 < c ⟨0, by omega⟩) (h1 : 0 < c ⟨1, by omega⟩)
    (h2 : c ⟨2, by omega⟩ = 0) :
    ∃ (σ : Fin 4 → Equiv.Perm (Fin n)) (t : Fin 4 → Fin n → ℤ),
      (∀ i, SpIsSign (t i)) ∧
      Function.Injective (fun i => spAct (σ i) (t i) c) ∧
      ∀ i, 0 < spAct (σ i) (t i) c ⟨0, by omega⟩ := by
  let σ : Fin 4 → Equiv.Perm (Fin n) :=
    ![Equiv.refl _, Equiv.refl _, Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩,
      Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩]
  let t : Fin 4 → Fin n → ℤ :=
    ![1, spSgn ⟨1, by omega⟩, 1, spSgn ⟨1, by omega⟩]
  have hσ0 : σ 0 = Equiv.refl (Fin n) := rfl
  have hσ1 : σ 1 = Equiv.refl (Fin n) := rfl
  have hσ2 : σ 2 = Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩ := rfl
  have hσ3 : σ 3 = Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩ := rfl
  have ht0 : t 0 = (1 : Fin n → ℤ) := rfl
  have ht1 : t 1 = spSgn ⟨1, by omega⟩ := rfl
  have ht2 : t 2 = (1 : Fin n → ℤ) := rfl
  have ht3 : t 3 = spSgn ⟨1, by omega⟩ := rfl
  refine ⟨σ, t, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [ht0, ht1, ht2, ht3, spIsSign_one, spIsSign_spSgn]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | (exfalso
         have hc1 := congrFun hij ⟨1, by omega⟩
         have hc2 := congrFun hij ⟨2, by omega⟩
         simp [spAct, hσ0, hσ1, hσ2, hσ3, ht0, ht1, ht2, ht3, Equiv.symm_swap,
           Equiv.refl_symm, Equiv.swap_apply_left, Equiv.swap_apply_right,
           spSgn, h2] at hc1 hc2
         omega)
  · intro i
    fin_cases i <;>
      simp [spAct, hσ0, hσ1, hσ2, hσ3, ht0, ht1, ht2, ht3, Equiv.symm_swap,
        Equiv.refl_symm,
        Equiv.swap_apply_of_ne_of_ne, spSgn, h0]

private lemma spWitness_neg_pos {n : ℕ} (hn : 3 ≤ n) {c : Fin n → ℤ}
    (h0 : 0 < c ⟨0, by omega⟩) (h1 : 0 < c ⟨1, by omega⟩) (h2 : 0 < c ⟨2, by omega⟩) :
    ∃ (σ : Fin 4 → Equiv.Perm (Fin n)) (t : Fin 4 → Fin n → ℤ),
      (∀ i, SpIsSign (t i)) ∧
      Function.Injective (fun i => spAct (σ i) (t i) c) ∧
      ∀ i, 0 < spAct (σ i) (t i) c ⟨0, by omega⟩ := by
  let σ : Fin 4 → Equiv.Perm (Fin n) := fun _ => Equiv.refl _
  let A : Finset (Fin n) := {⟨1, by omega⟩, ⟨2, by omega⟩}
  let t : Fin 4 → Fin n → ℤ :=
    ![1, spSgn ⟨1, by omega⟩, spSgn ⟨2, by omega⟩, spSgnOn A]
  have hσ : ∀ i, σ i = Equiv.refl (Fin n) := fun _ => rfl
  have ht0 : t 0 = (1 : Fin n → ℤ) := rfl
  have ht1 : t 1 = spSgn ⟨1, by omega⟩ := rfl
  have ht2 : t 2 = spSgn ⟨2, by omega⟩ := rfl
  have ht3 : t 3 = spSgnOn A := rfl
  refine ⟨σ, t, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [ht0, ht1, ht2, ht3, spIsSign_one, spIsSign_spSgn,
      spIsSign_spSgnOn]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | (exfalso
         have hc1 := congrFun hij ⟨1, by omega⟩
         have hc2 := congrFun hij ⟨2, by omega⟩
         simp [spAct, hσ, ht0, ht1, ht2, ht3, Equiv.refl_symm, spSgn, spSgnOn, A, Finset.mem_insert,
           Finset.mem_singleton] at hc1 hc2
         omega)
  · intro i
    fin_cases i <;>
      simp [spAct, hσ, ht0, ht1, ht2, ht3, Equiv.refl_symm, spSgn, spSgnOn, A,
        Finset.mem_insert, Finset.mem_singleton, h0]

private lemma spWitness_sum_lt {n : ℕ} (hn : 3 ≤ n) {c : Fin n → ℤ}
    (h0 : 0 < c ⟨0, by omega⟩) (h1 : 0 < c ⟨1, by omega⟩)
    (hlt : c ⟨1, by omega⟩ < c ⟨0, by omega⟩) :
    ∃ (σ : Fin 4 → Equiv.Perm (Fin n)) (t : Fin 4 → Fin n → ℤ),
      (∀ i, SpIsSign (t i)) ∧
      Function.Injective (fun i => spAct (σ i) (t i) c) ∧
      ∀ i, 0 < spAct (σ i) (t i) c ⟨0, by omega⟩ +
        spAct (σ i) (t i) c ⟨1, by omega⟩ := by
  let σ : Fin 4 → Equiv.Perm (Fin n) :=
    ![Equiv.refl _, Equiv.refl _, Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩,
      Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩]
  let t : Fin 4 → Fin n → ℤ :=
    ![1, spSgn ⟨1, by omega⟩, 1, spSgn ⟨1, by omega⟩]
  have hσ0 : σ 0 = Equiv.refl (Fin n) := rfl
  have hσ1 : σ 1 = Equiv.refl (Fin n) := rfl
  have hσ2 : σ 2 = Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ := rfl
  have hσ3 : σ 3 = Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ := rfl
  have ht0 : t 0 = (1 : Fin n → ℤ) := rfl
  have ht1 : t 1 = spSgn ⟨1, by omega⟩ := rfl
  have ht2 : t 2 = (1 : Fin n → ℤ) := rfl
  have ht3 : t 3 = spSgn ⟨1, by omega⟩ := rfl
  refine ⟨σ, t, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [ht0, ht1, ht2, ht3, spIsSign_one, spIsSign_spSgn]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | (exfalso
         have hc0 := congrFun hij ⟨0, by omega⟩
         have hc1 := congrFun hij ⟨1, by omega⟩
         simp [spAct, hσ0, hσ1, hσ2, hσ3, ht0, ht1, ht2, ht3, Equiv.symm_swap,
           Equiv.refl_symm, Equiv.swap_apply_left, Equiv.swap_apply_right,
           spSgn] at hc0 hc1
         omega)
  · intro i
    fin_cases i <;>
      simp [spAct, hσ0, hσ1, hσ2, hσ3, ht0, ht1, ht2, ht3, Equiv.symm_swap,
        Equiv.refl_symm, Equiv.swap_apply_left, Equiv.swap_apply_right,
        spSgn]
    all_goals omega

private lemma spWitness_sum_eq_zero {n : ℕ} (hn : 3 ≤ n) {c : Fin n → ℤ}
    (heq : c ⟨1, by omega⟩ = c ⟨0, by omega⟩)
    (h0 : 0 < c ⟨0, by omega⟩) (h2 : c ⟨2, by omega⟩ = 0) :
    ∃ (σ : Fin 4 → Equiv.Perm (Fin n)) (t : Fin 4 → Fin n → ℤ),
      (∀ i, SpIsSign (t i)) ∧
      Function.Injective (fun i => spAct (σ i) (t i) c) ∧
      ∀ i, 0 < spAct (σ i) (t i) c ⟨0, by omega⟩ +
        spAct (σ i) (t i) c ⟨1, by omega⟩ := by
  let σ : Fin 4 → Equiv.Perm (Fin n) :=
    ![Equiv.refl _, Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩,
      Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩,
      Equiv.swap ⟨0, by omega⟩ ⟨2, by omega⟩]
  let t : Fin 4 → Fin n → ℤ :=
    ![1, 1, spSgn ⟨1, by omega⟩, 1]
  have hσ0 : σ 0 = Equiv.refl (Fin n) := rfl
  have hσ1 : σ 1 = Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩ := rfl
  have hσ2 : σ 2 = Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩ := rfl
  have hσ3 : σ 3 = Equiv.swap ⟨0, by omega⟩ ⟨2, by omega⟩ := rfl
  have ht0 : t 0 = (1 : Fin n → ℤ) := rfl
  have ht1 : t 1 = (1 : Fin n → ℤ) := rfl
  have ht2 : t 2 = spSgn ⟨1, by omega⟩ := rfl
  have ht3 : t 3 = (1 : Fin n → ℤ) := rfl
  refine ⟨σ, t, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [ht0, ht1, ht2, ht3, spIsSign_one, spIsSign_spSgn]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | (exfalso
         have hc0 := congrFun hij ⟨0, by omega⟩
         have hc1 := congrFun hij ⟨1, by omega⟩
         have hc2 := congrFun hij ⟨2, by omega⟩
         simp [spAct, hσ0, hσ1, hσ2, hσ3, ht0, ht1, ht2, ht3, Equiv.symm_swap,
           Equiv.refl_symm, Equiv.swap_apply_left, Equiv.swap_apply_right,
           Equiv.swap_apply_of_ne_of_ne, spSgn, heq, h2] at hc0 hc1 hc2
         omega)
  · intro i
    fin_cases i <;>
      simp [spAct, hσ0, hσ1, hσ2, hσ3, ht0, ht1, ht2, ht3, Equiv.symm_swap,
        Equiv.refl_symm, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne, spSgn, heq, h2]
    all_goals omega

private lemma spWitness_sum_eq_mid {n : ℕ} (hn : 3 ≤ n) {c : Fin n → ℤ}
    (heq : c ⟨1, by omega⟩ = c ⟨0, by omega⟩) (h0 : 0 < c ⟨0, by omega⟩)
    (h2pos : 1 ≤ c ⟨2, by omega⟩) (hlt : c ⟨2, by omega⟩ < c ⟨1, by omega⟩) :
    ∃ (σ : Fin 4 → Equiv.Perm (Fin n)) (t : Fin 4 → Fin n → ℤ),
      (∀ i, SpIsSign (t i)) ∧
      Function.Injective (fun i => spAct (σ i) (t i) c) ∧
      ∀ i, 0 < spAct (σ i) (t i) c ⟨0, by omega⟩ +
        spAct (σ i) (t i) c ⟨1, by omega⟩ := by
  let σ : Fin 4 → Equiv.Perm (Fin n) :=
    ![Equiv.refl _, Equiv.refl _, Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩,
      Equiv.swap ⟨0, by omega⟩ ⟨2, by omega⟩]
  let t : Fin 4 → Fin n → ℤ :=
    ![1, spSgn ⟨2, by omega⟩, 1, 1]
  have hσ0 : σ 0 = Equiv.refl (Fin n) := rfl
  have hσ1 : σ 1 = Equiv.refl (Fin n) := rfl
  have hσ2 : σ 2 = Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩ := rfl
  have hσ3 : σ 3 = Equiv.swap ⟨0, by omega⟩ ⟨2, by omega⟩ := rfl
  have ht0 : t 0 = (1 : Fin n → ℤ) := rfl
  have ht1 : t 1 = spSgn ⟨2, by omega⟩ := rfl
  have ht2 : t 2 = (1 : Fin n → ℤ) := rfl
  have ht3 : t 3 = (1 : Fin n → ℤ) := rfl
  refine ⟨σ, t, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [ht0, ht1, ht2, ht3, spIsSign_one, spIsSign_spSgn]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | (exfalso
         have hc0 := congrFun hij ⟨0, by omega⟩
         have hc1 := congrFun hij ⟨1, by omega⟩
         have hc2 := congrFun hij ⟨2, by omega⟩
         simp [spAct, hσ0, hσ1, hσ2, hσ3, ht0, ht1, ht2, ht3, Equiv.symm_swap,
           Equiv.refl_symm, Equiv.swap_apply_left, Equiv.swap_apply_right,
           Equiv.swap_apply_of_ne_of_ne, spSgn, heq] at hc0 hc1 hc2
         omega)
  · intro i
    fin_cases i <;>
      simp [spAct, hσ0, hσ1, hσ2, hσ3, ht0, ht1, ht2, ht3, Equiv.symm_swap,
        Equiv.refl_symm, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne, spSgn, heq]
    all_goals omega

private lemma spWitness_sum_eq_top_zero {n : ℕ} (hn : 4 ≤ n) {c : Fin n → ℤ}
    (heq : c ⟨1, by omega⟩ = c ⟨0, by omega⟩)
    (heq2 : c ⟨2, by omega⟩ = c ⟨1, by omega⟩)
    (h0 : 0 < c ⟨0, by omega⟩) (h3 : c ⟨3, by omega⟩ = 0) :
    ∃ (σ : Fin 4 → Equiv.Perm (Fin n)) (t : Fin 4 → Fin n → ℤ),
      (∀ i, SpIsSign (t i)) ∧
      Function.Injective (fun i => spAct (σ i) (t i) c) ∧
      ∀ i, 0 < spAct (σ i) (t i) c ⟨0, by omega⟩ +
        spAct (σ i) (t i) c ⟨1, by omega⟩ := by
  let σ : Fin 4 → Equiv.Perm (Fin n) :=
    ![Equiv.refl _, Equiv.refl _, Equiv.swap ⟨2, by omega⟩ ⟨3, by omega⟩,
      Equiv.swap ⟨2, by omega⟩ ⟨3, by omega⟩]
  let t : Fin 4 → Fin n → ℤ :=
    ![1, spSgn ⟨2, by omega⟩, 1, spSgn ⟨2, by omega⟩]
  have hσ0 : σ 0 = Equiv.refl (Fin n) := rfl
  have hσ1 : σ 1 = Equiv.refl (Fin n) := rfl
  have hσ2 : σ 2 = Equiv.swap ⟨2, by omega⟩ ⟨3, by omega⟩ := rfl
  have hσ3 : σ 3 = Equiv.swap ⟨2, by omega⟩ ⟨3, by omega⟩ := rfl
  have ht0 : t 0 = (1 : Fin n → ℤ) := rfl
  have ht1 : t 1 = spSgn ⟨2, by omega⟩ := rfl
  have ht2 : t 2 = (1 : Fin n → ℤ) := rfl
  have ht3 : t 3 = spSgn ⟨2, by omega⟩ := rfl
  refine ⟨σ, t, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [ht0, ht1, ht2, ht3, spIsSign_one, spIsSign_spSgn]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | (exfalso
         have hc0 := congrFun hij ⟨0, by omega⟩
         have hc1 := congrFun hij ⟨1, by omega⟩
         have hc2 := congrFun hij ⟨2, by omega⟩
         have hc3 := congrFun hij ⟨3, by omega⟩
         simp [spAct, hσ0, hσ1, hσ2, hσ3, ht0, ht1, ht2, ht3, Equiv.symm_swap,
           Equiv.refl_symm, Equiv.swap_apply_left, Equiv.swap_apply_right,
           Equiv.swap_apply_of_ne_of_ne, spSgn, heq, heq2, h3] at hc0 hc1 hc2 hc3
         omega)
  · intro i
    fin_cases i <;>
      simp [spAct, hσ0, hσ1, hσ2, hσ3, ht0, ht1, ht2, ht3, Equiv.symm_swap,
        Equiv.refl_symm,
        Equiv.swap_apply_of_ne_of_ne, spSgn, heq]
    all_goals omega

private lemma spWitness_sum_eq_top_pos {n : ℕ} (hn : 4 ≤ n) {c : Fin n → ℤ}
    (heq : c ⟨1, by omega⟩ = c ⟨0, by omega⟩)
    (heq2 : c ⟨2, by omega⟩ = c ⟨1, by omega⟩)
    (h0 : 0 < c ⟨0, by omega⟩) (h3pos : 0 < c ⟨3, by omega⟩) :
    ∃ (σ : Fin 4 → Equiv.Perm (Fin n)) (t : Fin 4 → Fin n → ℤ),
      (∀ i, SpIsSign (t i)) ∧
      Function.Injective (fun i => spAct (σ i) (t i) c) ∧
      ∀ i, 0 < spAct (σ i) (t i) c ⟨0, by omega⟩ +
        spAct (σ i) (t i) c ⟨1, by omega⟩ := by
  let σ : Fin 4 → Equiv.Perm (Fin n) := fun _ => Equiv.refl _
  let A : Finset (Fin n) := {⟨2, by omega⟩, ⟨3, by omega⟩}
  let t : Fin 4 → Fin n → ℤ :=
    ![1, spSgn ⟨2, by omega⟩, spSgn ⟨3, by omega⟩, spSgnOn A]
  have hσ : ∀ i, σ i = Equiv.refl (Fin n) := fun _ => rfl
  have ht0 : t 0 = (1 : Fin n → ℤ) := rfl
  have ht1 : t 1 = spSgn ⟨2, by omega⟩ := rfl
  have ht2 : t 2 = spSgn ⟨3, by omega⟩ := rfl
  have ht3 : t 3 = spSgnOn A := rfl
  refine ⟨σ, t, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [ht0, ht1, ht2, ht3, spIsSign_one, spIsSign_spSgn,
      spIsSign_spSgnOn]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | (exfalso
         have hc2 := congrFun hij ⟨2, by omega⟩
         have hc3 := congrFun hij ⟨3, by omega⟩
         simp [spAct, hσ, ht0, ht1, ht2, ht3, Equiv.refl_symm, spSgn, spSgnOn, A,
           Finset.mem_insert, Finset.mem_singleton, heq, heq2] at hc2 hc3
         omega)
  · intro i
    fin_cases i <;>
      simp [spAct, hσ, ht0, ht1, ht2, ht3, Equiv.refl_symm, spSgn, spSgnOn, A,
        Finset.mem_insert, Finset.mem_singleton, heq]
    all_goals omega

private lemma spWitness_notMem_zero {n : ℕ} (hn : 3 ≤ n) {S : Finset (Fin n)}
    (h : spTypeVec S ⟨1, by omega⟩ = spTypeVec S ⟨0, by omega⟩) :
    (⟨0, by omega⟩ : Fin n) ∉ S := by
  have hs := spTypeVec_succ S ⟨0, by omega⟩ (by show 1 < n; omega)
  rw [h] at hs
  by_contra hmem
  rw [if_pos hmem] at hs
  omega

private lemma spWitness_notMem_one {n : ℕ} (hn : 3 ≤ n) {S : Finset (Fin n)}
    (h : spTypeVec S ⟨2, by omega⟩ = spTypeVec S ⟨1, by omega⟩) :
    (⟨1, by omega⟩ : Fin n) ∉ S := by
  have hs := spTypeVec_succ S ⟨1, by omega⟩ (by show 2 < n; omega)
  rw [h] at hs
  by_contra hmem
  rw [if_pos hmem] at hs
  omega

private lemma spWitness_subset_two {n : ℕ} (h3 : n = 3) {S : Finset (Fin n)}
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (h1 : (⟨1, by omega⟩ : Fin n) ∉ S) :
    S ⊆ {⟨2, by omega⟩} := by
  intro x hx
  rw [Finset.mem_singleton]
  have hxlt : x.val < 3 := by have := x.isLt; omega
  have hx0 : x.val ≠ 0 := by
    intro hval
    have hxeq : x = ⟨0, by omega⟩ := Fin.ext hval
    rw [hxeq] at hx
    exact h0 hx
  have hx1 : x.val ≠ 1 := by
    intro hval
    have hxeq : x = ⟨1, by omega⟩ := Fin.ext hval
    rw [hxeq] at hx
    exact h1 hx
  exact Fin.ext (by show x.val = 2; omega)

private lemma spTypeVec_four_le {n : ℕ} (hn : 3 ≤ n) {S : Finset (Fin n)} (hS : S.Nonempty)
    (hspin : n = 3 → S ≠ {⟨2, by omega⟩})
    (h01 : spTypeVec S ⟨1, by omega⟩ = spTypeVec S ⟨0, by omega⟩)
    (h12 : spTypeVec S ⟨2, by omega⟩ = spTypeVec S ⟨1, by omega⟩) :
    4 ≤ n := by
  by_contra h4
  have h3 : n = 3 := by omega
  have hnot0 := spWitness_notMem_zero hn h01
  have hnot1 := spWitness_notMem_one hn h12
  have hsub : S ⊆ {⟨2, by omega⟩} := spWitness_subset_two h3 hnot0 hnot1
  have h2mem : (⟨2, by omega⟩ : Fin n) ∈ S := by
    obtain ⟨x, hx⟩ := hS
    have hxeq : x = ⟨2, by omega⟩ := by simpa using hsub hx
    simpa [hxeq] using hx
  apply hspin h3
  ext y
  rw [Finset.mem_singleton]
  constructor
  · intro hy; simpa using hsub hy
  · intro hy; rw [hy]; exact h2mem

private lemma spWitness_base {n : ℕ} (hn : 3 ≤ n) {S : Finset (Fin n)} (hS : S.Nonempty)
    (hS0 : S ≠ {⟨0, by omega⟩}) :
    0 < spTypeVec S ⟨0, by omega⟩ ∧ 0 < spTypeVec S ⟨1, by omega⟩ ∧
    spTypeVec S ⟨1, by omega⟩ ≤ spTypeVec S ⟨0, by omega⟩ ∧
    spTypeVec S ⟨2, by omega⟩ ≤ spTypeVec S ⟨1, by omega⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [spTypeVec_zero (by omega) S]
    exact_mod_cast Finset.card_pos.mpr hS
  · have := spTypeVec_one_pos hn hS hS0
    omega
  · exact spTypeVec_anti S (by rw [Fin.le_iff_val_le_val]; norm_num)
  · exact spTypeVec_anti S (by rw [Fin.le_iff_val_le_val]; norm_num)

private lemma spWitness_neg_finish {n : ℕ} (hn : 0 < n) {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hπ : π ⟨0, by omega⟩ = ⟨0, by omega⟩) (hs : s ⟨0, by omega⟩ = -1)
    {c : Fin n → ℤ}
    (h : ∃ (σ : Fin 4 → Equiv.Perm (Fin n)) (t : Fin 4 → Fin n → ℤ),
      (∀ i, SpIsSign (t i)) ∧
      Function.Injective (fun i => spAct (σ i) (t i) c) ∧
      ∀ i, 0 < spAct (σ i) (t i) c ⟨0, by omega⟩) :
    ∃ (σ : Fin 4 → Equiv.Perm (Fin n)) (t : Fin 4 → Fin n → ℤ),
      (∀ i, SpIsSign (t i)) ∧
      Function.Injective (fun i => spAct (σ i) (t i) c) ∧
      ∀ i j, spAct (σ i) (t i) c ≠ spAct π s (spAct (σ j) (t j) c) := by
  obtain ⟨σ, t, ht, hinj, hpos⟩ := h
  exact ⟨σ, t, ht, hinj, fun i j => spAct_ne_of_neg hn hπ hs (hpos i) (hpos j)⟩

private lemma spWitness_sum_finish {n : ℕ} (hn : 2 ≤ n) {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hπ0 : π ⟨0, by omega⟩ = ⟨1, by omega⟩)
    (hπ1 : π ⟨1, by omega⟩ = ⟨0, by omega⟩) (hs0 : s ⟨0, by omega⟩ = -1)
    (hs1 : s ⟨1, by omega⟩ = -1) {c : Fin n → ℤ}
    (h : ∃ (σ : Fin 4 → Equiv.Perm (Fin n)) (t : Fin 4 → Fin n → ℤ),
      (∀ i, SpIsSign (t i)) ∧
      Function.Injective (fun i => spAct (σ i) (t i) c) ∧
      ∀ i, 0 < spAct (σ i) (t i) c ⟨0, by omega⟩ +
        spAct (σ i) (t i) c ⟨1, by omega⟩) :
    ∃ (σ : Fin 4 → Equiv.Perm (Fin n)) (t : Fin 4 → Fin n → ℤ),
      (∀ i, SpIsSign (t i)) ∧
      Function.Injective (fun i => spAct (σ i) (t i) c) ∧
      ∀ i j, spAct (σ i) (t i) c ≠ spAct π s (spAct (σ j) (t j) c) := by
  obtain ⟨σ, t, ht, hinj, hpos⟩ := h
  exact ⟨σ, t, ht, hinj, fun i j => spAct_ne_of_sum hn hπ0 hπ1 hs0 hs1 (hpos i) (hpos j)⟩

theorem exists_four_spWitness_of_antitone {n : ℕ} (hn : 3 ≤ n) {c : Fin n → ℤ}
    (hanti : Antitone c) (hnonneg : ∀ a, 0 ≤ c a) (h1 : 0 < c ⟨1, by omega⟩)
    (hcube : n = 3 → c ⟨2, by omega⟩ ≠ c ⟨0, by omega⟩) {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ}
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = -1 ∧ s ⟨1, by omega⟩ = -1)) :
    ∃ (σ : Fin 4 → Equiv.Perm (Fin n)) (t : Fin 4 → Fin n → ℤ), (∀ i, SpIsSign (t i)) ∧
      Function.Injective (fun i => spAct (σ i) (t i) c) ∧
      ∀ i j, spAct (σ i) (t i) c ≠ spAct π s (spAct (σ j) (t j) c) := by
  have hn0 : 0 < n := by omega
  have hle : c ⟨1, by omega⟩ ≤ c ⟨0, by omega⟩ := hanti (by rw [Fin.le_iff_val_le_val]; norm_num)
  have hle2 : c ⟨2, by omega⟩ ≤ c ⟨1, by omega⟩ := hanti (by rw [Fin.le_iff_val_le_val]; norm_num)
  have h0 : 0 < c ⟨0, by omega⟩ := lt_of_lt_of_le h1 hle
  rcases hx with ⟨hπ0, hs0⟩ | ⟨hπ01, hπ10, hs0, hs1⟩
  · by_cases hc2 : c ⟨2, by omega⟩ = 0
    · exact spWitness_neg_finish hn0 hπ0 hs0 (spWitness_neg_zero hn h0 h1 hc2)
    · have h2 : 0 < c ⟨2, by omega⟩ := by
        have := hnonneg ⟨2, by omega⟩
        omega
      exact spWitness_neg_finish hn0 hπ0 hs0 (spWitness_neg_pos hn h0 h1 h2)
  · rcases lt_or_eq_of_le hle with hlt | heq
    · exact spWitness_sum_finish (by omega) hπ01 hπ10 hs0 hs1
        (spWitness_sum_lt hn h0 h1 hlt)
    · by_cases hc2 : c ⟨2, by omega⟩ = 0
      · exact spWitness_sum_finish (by omega) hπ01 hπ10 hs0 hs1
          (spWitness_sum_eq_zero hn heq h0 hc2)
      · have h2pos : 1 ≤ c ⟨2, by omega⟩ := by
          have := hnonneg ⟨2, by omega⟩
          omega
        rcases lt_or_eq_of_le hle2 with hlt2 | heq2
        · exact spWitness_sum_finish (by omega) hπ01 hπ10 hs0 hs1
            (spWitness_sum_eq_mid hn heq h0 h2pos hlt2)
        · have hn4 : 4 ≤ n := by
            by_contra h4
            exact hcube (by omega) (heq2.trans heq)
          by_cases h3 : c ⟨3, by omega⟩ = 0
          · exact spWitness_sum_finish (by omega) hπ01 hπ10 hs0 hs1
              (spWitness_sum_eq_top_zero hn4 heq heq2 h0 h3)
          · have h3pos : 0 < c ⟨3, by omega⟩ := by
              have := hnonneg ⟨3, by omega⟩
              omega
            exact spWitness_sum_finish (by omega) hπ01 hπ10 hs0 hs1
              (spWitness_sum_eq_top_pos hn4 heq heq2 h0 h3pos)

theorem exists_four_spWitness {n : ℕ} (hn : 3 ≤ n) {S : Finset (Fin n)} (hS : S.Nonempty)
    (hS0 : S ≠ {⟨0, by omega⟩}) (hspin : n = 3 → S ≠ {⟨2, by omega⟩})
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = -1 ∧ s ⟨1, by omega⟩ = -1)) :
    ∃ (σ : Fin 4 → Equiv.Perm (Fin n)) (t : Fin 4 → Fin n → ℤ), (∀ i, SpIsSign (t i)) ∧
      Function.Injective (fun i => spAct (σ i) (t i) (spTypeVec S)) ∧
      ∀ i j, spAct (σ i) (t i) (spTypeVec S) ≠ spAct π s (spAct (σ j) (t j) (spTypeVec S)) := by
  have hanti : Antitone (spTypeVec S) := fun a b hab => spTypeVec_anti S hab
  have h1 : 0 < spTypeVec S ⟨1, by omega⟩ := (spWitness_base hn hS hS0).2.1
  have hcube : n = 3 → spTypeVec S ⟨2, by omega⟩ ≠ spTypeVec S ⟨0, by omega⟩ := by
    intro h3 heq20
    have h10 : spTypeVec S ⟨1, by omega⟩ ≤ spTypeVec S ⟨0, by omega⟩ :=
      spTypeVec_anti S (by rw [Fin.le_iff_val_le_val]; norm_num)
    have h21 : spTypeVec S ⟨2, by omega⟩ ≤ spTypeVec S ⟨1, by omega⟩ :=
      spTypeVec_anti S (by rw [Fin.le_iff_val_le_val]; norm_num)
    have h01 : spTypeVec S ⟨1, by omega⟩ = spTypeVec S ⟨0, by omega⟩ :=
      le_antisymm h10 (heq20 ▸ h21)
    have h12 : spTypeVec S ⟨2, by omega⟩ = spTypeVec S ⟨1, by omega⟩ :=
      le_antisymm h21 (heq20.symm ▸ h10)
    have := spTypeVec_four_le hn hS hspin h01 h12
    omega
  exact exists_four_spWitness_of_antitone hn hanti (spTypeVec_nonneg S) h1 hcube hx

end CFSG.LocalAnalysis.WeakClosure81

module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpWitness

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.StandardType

@[expose] def omqnfFunA (m r : ℕ) (a : Fin m) : Fin m :=
  if h : a.val < 2 * r ∧ a.val % 2 = 0 ∧ a.val + 1 < m then ⟨a.val + 1, h.2.2⟩
  else if _ : a.val < 2 * r ∧ a.val % 2 = 1 then ⟨a.val - 1, by have := a.isLt; omega⟩
  else a

private theorem omqnfdf_funA_val (m r : ℕ) (a : Fin m) : (omqnfFunA m r a).val =
    if a.val < 2 * r ∧ a.val % 2 = 0 ∧ a.val + 1 < m then a.val + 1
    else if a.val < 2 * r ∧ a.val % 2 = 1 then a.val - 1 else a.val := by
  unfold omqnfFunA
  split_ifs <;> rfl

theorem omqnfFunA_involutive (m r : ℕ) : Function.Involutive (omqnfFunA m r) := by
  intro a
  apply Fin.ext
  have h := a.isLt
  rw [omqnfdf_funA_val, omqnfdf_funA_val]
  split_ifs <;> omega

@[expose] def omqnfPermA (m r : ℕ) : Equiv.Perm (Fin m) :=
  Function.Involutive.toPerm _ (omqnfFunA_involutive m r)

@[expose] def omqnfSignC (m j : ℕ) : Fin m → ℤ := fun a => if a.val < j then -1 else 1

theorem omqnfPermA_mul_self (m r : ℕ) : omqnfPermA m r * omqnfPermA m r = 1 := by
  refine Equiv.ext fun a => ?_
  exact omqnfFunA_involutive m r a

theorem omqnfPermA_zero {m r : ℕ} (h1 : 1 ≤ r) (h2 : 2 * r ≤ m) :
    omqnfPermA m r ⟨0, by omega⟩ = ⟨1, by omega⟩ := by
  apply Fin.ext
  show (omqnfFunA m r ⟨0, by omega⟩).val = 1
  rw [omqnfdf_funA_val]
  have h3 : (⟨0, by omega⟩ : Fin m).val < 2 * r ∧ (⟨0, by omega⟩ : Fin m).val % 2 = 0 ∧
      (⟨0, by omega⟩ : Fin m).val + 1 < m := by
    show 0 < 2 * r ∧ 0 % 2 = 0 ∧ 0 + 1 < m
    omega
  rw [if_pos h3]

theorem omqnfPermA_one {m r : ℕ} (h1 : 1 ≤ r) (h2 : 2 * r ≤ m) :
    omqnfPermA m r ⟨1, by omega⟩ = ⟨0, by omega⟩ := by
  apply Fin.ext
  show (omqnfFunA m r ⟨1, by omega⟩).val = 0
  rw [omqnfdf_funA_val]
  have h3 : ¬ ((⟨1, by omega⟩ : Fin m).val < 2 * r ∧ (⟨1, by omega⟩ : Fin m).val % 2 = 0 ∧
      (⟨1, by omega⟩ : Fin m).val + 1 < m) := by
    show ¬ (1 < 2 * r ∧ 1 % 2 = 0 ∧ 1 + 1 < m)
    omega
  have h4 : (⟨1, by omega⟩ : Fin m).val < 2 * r ∧ (⟨1, by omega⟩ : Fin m).val % 2 = 1 := by
    show 1 < 2 * r ∧ 1 % 2 = 1
    omega
  rw [if_neg h3, if_pos h4]
  rfl

theorem omqnfSignC_isSign (m j : ℕ) : SpIsSign (omqnfSignC m j) := by
  intro a
  unfold omqnfSignC
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem omqnfSignC_zero {m j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ m) :
    omqnfSignC m j ⟨0, by omega⟩ = -1 := by
  unfold omqnfSignC
  rw [if_pos (by show 0 < j; omega)]

private theorem omqnfdf_filter_lt (m j : ℕ) (h : j ≤ m) :
    (Finset.univ.filter fun a : Fin m => a.val < j).card = j := by
  have : (Finset.univ.filter fun a : Fin m => a.val < j).map Fin.valEmbedding =
      Finset.range j := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, this, Finset.card_range]

private theorem omqnfdf_card_sum {m : ℕ} (p : Fin m → Prop) [DecidablePred p] :
    (Finset.univ.filter fun x : Fin m ⊕ Fin m => p (Sum.elim id id x)).card =
      2 * (Finset.univ.filter p).card := by
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, id_eq]
  rw [two_mul]
  congr 1

theorem omqnfSignC_card {m j : ℕ} (h : j ≤ m) :
    (Finset.univ.filter fun a : Fin m => omqnfSignC m j a = -1).card = j := by
  have : (Finset.univ.filter fun a : Fin m => omqnfSignC m j a = -1) =
      Finset.univ.filter fun a : Fin m => a.val < j := by
    refine Finset.filter_congr fun a _ => ?_
    unfold omqnfSignC
    by_cases h' : a.val < j <;> simp [h']
  rw [this]
  exact omqnfdf_filter_lt m j h

theorem omqnfSignC_prod {m j : ℕ} (h : j ≤ m) : ∏ a, omqnfSignC m j a = (-1) ^ j := by
  have h1 : ∏ a, omqnfSignC m j a = ∏ a : Fin m, (if a.val < j then (-1 : ℤ) else 1) := rfl
  rw [h1, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
    omqnfdf_filter_lt m j h]

theorem omqnf_spMonoPerm_mul_self_A (m r : ℕ) :
    spMonoPerm (omqnfPermA m r) 1 * spMonoPerm (omqnfPermA m r) 1 = 1 := by
  have hπ : omqnfPermA m r * omqnfPermA m r = 1 := omqnfPermA_mul_self m r
  have h1 := spMonoPerm_mul (π₁ := omqnfPermA m r) (π₂ := omqnfPermA m r)
    (spIsSign_one (m := m)) (spIsSign_one (m := m))
  rw [← h1, hπ]
  have : (fun c : Fin m => (1 : Fin m → ℤ) c * (1 : Fin m → ℤ) (omqnfPermA m r c)) = 1 := by
    funext c; simp
  rw [this, spMonoPerm_one]

theorem omqnf_spMonoPerm_mul_self_C (m j : ℕ) :
    spMonoPerm (1 : Equiv.Perm (Fin m)) (omqnfSignC m j) *
      spMonoPerm (1 : Equiv.Perm (Fin m)) (omqnfSignC m j) = 1 := by
  have h1 := spMonoPerm_mul (π₁ := (1 : Equiv.Perm (Fin m))) (π₂ := 1)
    (omqnfSignC_isSign m j) (omqnfSignC_isSign m j)
  rw [← h1, mul_one]
  have : (fun c : Fin m => omqnfSignC m j c * omqnfSignC m j ((1 : Equiv.Perm (Fin m)) c)) =
      1 := by
    funext c
    simp only [Equiv.Perm.one_apply, Pi.one_apply]
    exact (omqnfSignC_isSign m j).mul_self c
  rw [this, spMonoPerm_one]

theorem omqnf_support_card_A {m r : ℕ} (h : 2 * r ≤ m) :
    (spMonoPerm (omqnfPermA m r) 1).support.card = 4 * r := by
  have hmoved : (spMonoPerm (omqnfPermA m r) 1).support =
      Finset.univ.filter fun x : Fin m ⊕ Fin m => (Sum.elim id id x).val < 2 * r := by
    ext x
    rw [Equiv.Perm.mem_support]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have key : ∀ a : Fin m, omqnfPermA m r a ≠ a ↔ a.val < 2 * r := by
      intro a
      have hv := omqnfdf_funA_val m r a
      have ha := a.isLt
      show omqnfFunA m r a ≠ a ↔ _
      rw [Ne, Fin.ext_iff, hv]
      split_ifs <;> omega
    rcases x with a | a
    · rw [spMonoPerm_inl]
      simp only [Pi.one_apply, if_true, ne_eq, Sum.inl.injEq, Sum.elim_inl, id_eq]
      exact key a
    · rw [spMonoPerm_inr]
      simp only [Pi.one_apply, if_true, ne_eq, Sum.inr.injEq, Sum.elim_inr, id_eq]
      exact key a
  rw [hmoved]
  have := omqnfdf_card_sum (m := m) (fun a => a.val < 2 * r)
  rw [this, omqnfdf_filter_lt m (2 * r) h]
  ring

theorem omqnf_support_card_C {m j : ℕ} (h : j ≤ m) :
    (spMonoPerm (1 : Equiv.Perm (Fin m)) (omqnfSignC m j)).support.card = 2 * j := by
  have hmoved : (spMonoPerm (1 : Equiv.Perm (Fin m)) (omqnfSignC m j)).support =
      Finset.univ.filter fun x : Fin m ⊕ Fin m => (Sum.elim id id x).val < j := by
    ext x
    rw [Equiv.Perm.mem_support]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases x with a | a
    · rw [spMonoPerm_inl]
      by_cases hs : a.val < j
      · have : omqnfSignC m j a ≠ 1 := by simp [omqnfSignC, hs]
        simp [this, hs]
      · have : omqnfSignC m j a = 1 := by simp [omqnfSignC, hs]
        simp [this, hs]
    · rw [spMonoPerm_inr]
      by_cases hs : a.val < j
      · have : omqnfSignC m j a ≠ 1 := by simp [omqnfSignC, hs]
        simp [this, hs]
      · have : omqnfSignC m j a = 1 := by simp [omqnfSignC, hs]
        simp [this, hs]
  rw [hmoved]
  have := omqnfdf_card_sum (m := m) (fun a => a.val < j)
  rw [this, omqnfdf_filter_lt m j h]

end CFSG.LocalAnalysis.WeakClosure81

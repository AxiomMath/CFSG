module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs

public section

namespace CFSG.StandardType

open Module

private noncomputable def ggQ2s4c_succAboveEquiv (m : ℕ) (p : Fin (m + 1)) :
    Fin m ≃ {i : Fin (m + 1) // i ≠ p} :=
  Equiv.ofBijective
    (fun i => (⟨p.succAbove i, p.succAbove_ne i⟩ : {i : Fin (m + 1) // i ≠ p}))
    ⟨fun _ _ hij => Fin.succAbove_right_injective (congrArg Subtype.val hij), fun y => by
      obtain ⟨i, hi⟩ := show y.1 ∈ Set.range p.succAbove from by
        rw [Fin.range_succAbove]; exact y.2
      exact ⟨i, Subtype.ext hi⟩⟩

private noncomputable def ggQ2s4c_complEquiv {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n) :
    Fin (n - 1) ≃ {i : Fin n // i ≠ a₀} :=
  (ggQ2s4c_succAboveEquiv (n - 1) (Fin.cast (Nat.sub_add_cancel hn).symm a₀)).trans
    (Equiv.subtypeEquiv (finCongr (Nat.sub_add_cancel hn)) (fun i => by
      have hkey : finCongr (Nat.sub_add_cancel hn) (Fin.cast (Nat.sub_add_cancel hn).symm a₀)
          = a₀ := by simp
      constructor
      · intro h he
        apply h
        simpa using congrArg (Fin.cast (Nat.sub_add_cancel hn).symm) he
      · intro h he
        exact h (by rw [he]; exact hkey)))

private noncomputable def ggQ2s4c_complEquivIf {n : ℕ} (p : Fin n) :
    Fin (n - 1) ≃ {i : Fin n // i ≠ p} where
  toFun i :=
    ⟨⟨if (i : ℕ) < (p : ℕ) then (i : ℕ) else (i : ℕ) + 1, by
        have hi := i.isLt; have hp := p.isLt
        split_ifs <;> omega⟩,
      by
        have hi := i.isLt; have hp := p.isLt
        intro h
        have hv : (if (i : ℕ) < (p : ℕ) then (i : ℕ) else (i : ℕ) + 1) = (p : ℕ) :=
          congrArg Fin.val h
        split_ifs at hv <;> omega⟩
  invFun j :=
    ⟨if (j : ℕ) < (p : ℕ) then (j : ℕ) else (j : ℕ) - 1, by
      have hj := j.1.isLt; have hp := p.isLt
      have hjne : (j : ℕ) ≠ (p : ℕ) := fun h => j.2 (Fin.ext h)
      split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext
    have hi := i.isLt; have hp := p.isLt
    simp only [Fin.val_mk]
    split_ifs <;> omega
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have hj := j.1.isLt; have hp := p.isLt
    have hjne : (j : ℕ) ≠ (p : ℕ) := fun h => j.2 (Fin.ext h)
    simp only [Fin.val_mk]
    split_ifs <;> omega

private lemma ggQ2s4c_complEquivIf_val {n : ℕ} (p : Fin n) (i : Fin (n - 1)) :
    ((ggQ2s4c_complEquivIf p i : Fin n) : ℕ) =
      (if (i : ℕ) < (p : ℕ) then (i : ℕ) else (i : ℕ) + 1) := rfl

private noncomputable def ggQ2s4c_equivOf {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {n m : ℕ}
    (e : Fin n ≃ D.ι) (a₀ : Fin n) (ha : e a₀ = D.a)
    (c : Fin m ≃ {i : Fin n // i ≠ a₀}) : Fin m ≃ {k : D.ι // k ≠ D.a} :=
  c.trans (Equiv.subtypeEquiv e (fun i => by
    constructor
    · intro hi heq
      exact hi (e.injective (by rw [ha]; exact heq))
    · intro hk hi
      exact hk (by rw [hi, ha])))

private lemma ggQ2s4c_equivOf_apply {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {n m : ℕ}
    (e : Fin n ≃ D.ι) (a₀ : Fin n) (ha : e a₀ = D.a)
    (c : Fin m ≃ {i : Fin n // i ≠ a₀}) (i : Fin m) :
    ((ggQ2s4c_equivOf D e a₀ ha c i : {k : D.ι // k ≠ D.a}) : D.ι) = e (c i) := rfl

private lemma ggQ2s4c_leaf_of_row {n : ℕ} (hn : 2 ≤ n) (M : Matrix (Fin n) (Fin n) ℤ)
    (a₀ : Fin n)
    (hprev : ∀ {i j : Fin n}, j.val + 1 = i.val → M i j ≠ 0)
    (hnext : ∀ {i j : Fin n}, i.val + 1 = j.val → M i j ≠ 0)
    (h : ∃! c, c ≠ a₀ ∧ M a₀ c ≠ 0) : a₀.val = 0 ∨ a₀.val = n - 1 := by
  rcases Nat.eq_zero_or_pos a₀.val with h0 | hpos
  · exact Or.inl h0
  · by_cases hlast : a₀.val = n - 1
    · exact Or.inr hlast
    · exfalso
      obtain ⟨c, _, huniq⟩ := h
      have hlt : a₀.val < n - 1 := by have := a₀.isLt; omega
      have hM1 : M a₀ ⟨a₀.val - 1, by omega⟩ ≠ 0 :=
        hprev (i := a₀) (j := ⟨a₀.val - 1, by omega⟩) (by simp only [Fin.val_mk]; omega)
      have hM2 : M a₀ ⟨a₀.val + 1, by omega⟩ ≠ 0 :=
        hnext (i := a₀) (j := ⟨a₀.val + 1, by omega⟩) (by simp only [Fin.val_mk])
      have hne1 : (⟨a₀.val - 1, by omega⟩ : Fin n) ≠ a₀ := by
        intro h'; have := congrArg Fin.val h'; simp at this; omega
      have hne2 : (⟨a₀.val + 1, by omega⟩ : Fin n) ≠ a₀ := by
        intro h'
        have h2 : a₀.val + 1 = a₀.val := congrArg Fin.val h'
        omega
      have hu1 := huniq _ ⟨hne1, hM1⟩
      have hu2 := huniq _ ⟨hne2, hM2⟩
      have hEq : (⟨a₀.val - 1, by omega⟩ : Fin n) = ⟨a₀.val + 1, by omega⟩ :=
        hu1.trans hu2.symm
      have h2 : a₀.val - 1 = a₀.val + 1 := by
        simpa using congrArg Fin.val hEq
      omega

private lemma ggQ2s4c_A_succ (m : ℕ) (i j : Fin m) :
    CartanMatrix.A (m + 1) (Fin.succ i) (Fin.succ j) = CartanMatrix.A m i j := by
  rw [CartanMatrix.A, CartanMatrix.A, Matrix.of_apply, Matrix.of_apply]
  simp only [Fin.val_succ, Fin.succ_inj]
  split_ifs <;> omega

private lemma ggQ2s4c_A_castSucc (m : ℕ) (i j : Fin m) :
    CartanMatrix.A (m + 1) (Fin.castSucc i) (Fin.castSucc j) = CartanMatrix.A m i j := by
  rw [CartanMatrix.A, CartanMatrix.A, Matrix.of_apply, Matrix.of_apply]
  simp only [Fin.val_castSucc, Fin.castSucc_inj]

private lemma ggQ2s4c_A_cast {m n : ℕ} (h : m = n) (i j : Fin m) :
    CartanMatrix.A n (Fin.cast h i) (Fin.cast h j) = CartanMatrix.A m i j := by
  subst h
  rfl

private lemma ggQ2s4c_A_prev {n : ℕ} {i j : Fin n} (hij : j.val + 1 = i.val) :
    CartanMatrix.A n i j = -1 := by
  have hne : i ≠ j := by intro h'; rw [h'] at hij; omega
  rw [CartanMatrix.A, Matrix.of_apply]
  rw [if_neg hne, if_pos (Or.inr hij)]

private lemma ggQ2s4c_A_next {n : ℕ} {i j : Fin n} (hij : i.val + 1 = j.val) :
    CartanMatrix.A n i j = -1 := by
  have hne : i ≠ j := by intro h'; rw [h'] at hij; omega
  rw [CartanMatrix.A, Matrix.of_apply]
  rw [if_neg hne, if_pos (Or.inl hij)]

private theorem ggQ2s4c_A_witness {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n)
    (h : a₀.val = 0 ∨ a₀.val = n - 1) :
    ∃ e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀},
      ∀ i j : Fin (n - 1),
        CartanMatrix.A n (e i) (e j) = CartanMatrix.A (n - 1) i j := by
  have hcast : n - 1 + 1 = n := Nat.sub_add_cancel hn
  let p : Fin (n - 1 + 1) := Fin.cast hcast.symm a₀
  let e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀} := ggQ2s4c_complEquiv hn a₀
  have he_val : ∀ i : Fin (n - 1), (e i).val = finCongr hcast (p.succAbove i) := fun i => rfl
  rcases h with h0 | hlast
  · have hp : p = 0 := by ext; simp [p, h0]
    refine ⟨e, fun i j => ?_⟩
    have hi : (e i).val = Fin.cast hcast (Fin.succ i) := by
      rw [he_val, hp, Fin.succAbove_zero]
      simp
    have hj : (e j).val = Fin.cast hcast (Fin.succ j) := by
      rw [he_val, hp, Fin.succAbove_zero]
      simp
    rw [hi, hj, ggQ2s4c_A_cast hcast]
    exact ggQ2s4c_A_succ (n - 1) i j
  · have hp : p = Fin.last (n - 1) := by
      ext
      simp [p, Fin.val_last]
      omega
    refine ⟨e, fun i j => ?_⟩
    have hi : (e i).val = Fin.cast hcast (Fin.castSucc i) := by
      rw [he_val, hp, Fin.succAbove_last]
      simp
    have hj : (e j).val = Fin.cast hcast (Fin.castSucc j) := by
      rw [he_val, hp, Fin.succAbove_last]
      simp
    rw [hi, hj, ggQ2s4c_A_cast hcast]
    exact ggQ2s4c_A_castSucc (n - 1) i j

private lemma ggQ2s4c_B_prev {n : ℕ} {i j : Fin n} (hij : j.val + 1 = i.val) :
    CartanMatrix.B n i j ≠ 0 := by
  have hne : i ≠ j := by intro h'; rw [h'] at hij; omega
  rw [CartanMatrix.B, Matrix.of_apply]
  rw [if_neg hne, if_neg (by omega), if_pos hij]
  decide

private lemma ggQ2s4c_B_next {n : ℕ} {i j : Fin n} (hij : i.val + 1 = j.val) :
    CartanMatrix.B n i j ≠ 0 := by
  have hne : i ≠ j := by intro h'; rw [h'] at hij; omega
  rw [CartanMatrix.B, Matrix.of_apply]
  rw [if_neg hne, if_pos hij]
  split_ifs <;> decide

private lemma ggQ2s4c_B_succ (m : ℕ) (i j : Fin m) :
    CartanMatrix.B (m + 1) (Fin.succ i) (Fin.succ j) = CartanMatrix.B m i j := by
  rw [CartanMatrix.B, CartanMatrix.B, Matrix.of_apply, Matrix.of_apply]
  simp only [Fin.val_succ, Fin.succ_inj]
  split_ifs <;> omega

private lemma ggQ2s4c_B_castSucc (m : ℕ) (i j : Fin m) :
    CartanMatrix.B (m + 1) (Fin.castSucc i) (Fin.castSucc j) = CartanMatrix.A m i j := by
  rw [CartanMatrix.B, CartanMatrix.A, Matrix.of_apply, Matrix.of_apply]
  simp only [Fin.val_castSucc, Fin.castSucc_inj]
  split_ifs <;> omega

private lemma ggQ2s4c_B_cast {m n : ℕ} (h : m = n) (i j : Fin m) :
    CartanMatrix.B n (Fin.cast h i) (Fin.cast h j) = CartanMatrix.B m i j := by
  subst h
  rfl

private theorem ggQ2s4c_B_witness {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n)
    (h : a₀.val = n - 1) :
    ∃ e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀},
      ∀ i j : Fin (n - 1),
        CartanMatrix.B n (e i) (e j) = CartanMatrix.A (n - 1) i j := by
  have hcast : n - 1 + 1 = n := Nat.sub_add_cancel hn
  let p : Fin (n - 1 + 1) := Fin.cast hcast.symm a₀
  let e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀} := ggQ2s4c_complEquiv hn a₀
  have he_val : ∀ i : Fin (n - 1), (e i).val = finCongr hcast (p.succAbove i) := fun i => rfl
  have hp : p = Fin.last (n - 1) := by
    ext
    simp [p, Fin.val_last]
    omega
  refine ⟨e, fun i j => ?_⟩
  have hi : (e i).val = Fin.cast hcast (Fin.castSucc i) := by
    rw [he_val, hp, Fin.succAbove_last]
    simp
  have hj : (e j).val = Fin.cast hcast (Fin.castSucc j) := by
    rw [he_val, hp, Fin.succAbove_last]
    simp
  rw [hi, hj, ggQ2s4c_B_cast hcast]
  exact ggQ2s4c_B_castSucc (n - 1) i j

private theorem ggQ2s4c_B_zero_witness {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n)
    (h : a₀.val = 0) :
    ∃ e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀},
      ∀ i j : Fin (n - 1),
        CartanMatrix.B n (e i) (e j) = CartanMatrix.B (n - 1) i j := by
  have hcast : n - 1 + 1 = n := Nat.sub_add_cancel hn
  let p : Fin (n - 1 + 1) := Fin.cast hcast.symm a₀
  let e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀} := ggQ2s4c_complEquiv hn a₀
  have he_val : ∀ i : Fin (n - 1), (e i).val = finCongr hcast (p.succAbove i) := fun i => rfl
  have hp : p = 0 := by ext; simp [p, h]
  refine ⟨e, fun i j => ?_⟩
  have hi : (e i).val = Fin.cast hcast (Fin.succ i) := by
    rw [he_val, hp, Fin.succAbove_zero]
    simp
  have hj : (e j).val = Fin.cast hcast (Fin.succ j) := by
    rw [he_val, hp, Fin.succAbove_zero]
    simp
  rw [hi, hj, ggQ2s4c_B_cast hcast]
  exact ggQ2s4c_B_succ (n - 1) i j

private lemma ggQ2s4c_B_one_eq_A (i j : Fin 1) :
    CartanMatrix.B 1 i j = CartanMatrix.A 1 i j := by
  fin_cases i; fin_cases j; decide

private lemma ggQ2s4c_C_prev {n : ℕ} {i j : Fin n} (hij : j.val + 1 = i.val) :
    CartanMatrix.C n i j ≠ 0 := by
  have hne : i ≠ j := by intro h'; rw [h'] at hij; omega
  rw [CartanMatrix.C, Matrix.of_apply]
  rw [if_neg hne, if_neg (by omega), if_pos hij]
  split_ifs <;> decide

private lemma ggQ2s4c_C_next {n : ℕ} {i j : Fin n} (hij : i.val + 1 = j.val) :
    CartanMatrix.C n i j ≠ 0 := by
  have hne : i ≠ j := by intro h'; rw [h'] at hij; omega
  rw [CartanMatrix.C, Matrix.of_apply]
  rw [if_neg hne, if_pos hij]
  decide

private lemma ggQ2s4c_C_succ (m : ℕ) (i j : Fin m) :
    CartanMatrix.C (m + 1) (Fin.succ i) (Fin.succ j) = CartanMatrix.C m i j := by
  rw [CartanMatrix.C, CartanMatrix.C, Matrix.of_apply, Matrix.of_apply]
  simp only [Fin.val_succ, Fin.succ_inj]
  split_ifs <;> omega

private lemma ggQ2s4c_C_castSucc (m : ℕ) (i j : Fin m) :
    CartanMatrix.C (m + 1) (Fin.castSucc i) (Fin.castSucc j) = CartanMatrix.A m i j := by
  rw [CartanMatrix.C, CartanMatrix.A, Matrix.of_apply, Matrix.of_apply]
  simp only [Fin.val_castSucc, Fin.castSucc_inj]
  split_ifs <;> omega

private lemma ggQ2s4c_C_cast {m n : ℕ} (h : m = n) (i j : Fin m) :
    CartanMatrix.C n (Fin.cast h i) (Fin.cast h j) = CartanMatrix.C m i j := by
  subst h
  rfl

private theorem ggQ2s4c_C_witness {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n)
    (h : a₀.val = n - 1) :
    ∃ e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀},
      ∀ i j : Fin (n - 1),
        CartanMatrix.C n (e i) (e j) = CartanMatrix.A (n - 1) i j := by
  have hcast : n - 1 + 1 = n := Nat.sub_add_cancel hn
  let p : Fin (n - 1 + 1) := Fin.cast hcast.symm a₀
  let e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀} := ggQ2s4c_complEquiv hn a₀
  have he_val : ∀ i : Fin (n - 1), (e i).val = finCongr hcast (p.succAbove i) := fun i => rfl
  have hp : p = Fin.last (n - 1) := by
    ext
    simp [p, Fin.val_last]
    omega
  refine ⟨e, fun i j => ?_⟩
  have hi : (e i).val = Fin.cast hcast (Fin.castSucc i) := by
    rw [he_val, hp, Fin.succAbove_last]
    simp
  have hj : (e j).val = Fin.cast hcast (Fin.castSucc j) := by
    rw [he_val, hp, Fin.succAbove_last]
    simp
  rw [hi, hj, ggQ2s4c_C_cast hcast]
  exact ggQ2s4c_C_castSucc (n - 1) i j

private theorem ggQ2s4c_C_zero_witness {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n)
    (h : a₀.val = 0) :
    ∃ e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀},
      ∀ i j : Fin (n - 1),
        CartanMatrix.C n (e i) (e j) = CartanMatrix.C (n - 1) i j := by
  have hcast : n - 1 + 1 = n := Nat.sub_add_cancel hn
  let p : Fin (n - 1 + 1) := Fin.cast hcast.symm a₀
  let e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀} := ggQ2s4c_complEquiv hn a₀
  have he_val : ∀ i : Fin (n - 1), (e i).val = finCongr hcast (p.succAbove i) := fun i => rfl
  have hp : p = 0 := by ext; simp [p, h]
  refine ⟨e, fun i j => ?_⟩
  have hi : (e i).val = Fin.cast hcast (Fin.succ i) := by
    rw [he_val, hp, Fin.succAbove_zero]
    simp
  have hj : (e j).val = Fin.cast hcast (Fin.succ j) := by
    rw [he_val, hp, Fin.succAbove_zero]
    simp
  rw [hi, hj, ggQ2s4c_C_cast hcast]
  exact ggQ2s4c_C_succ (n - 1) i j

private lemma ggQ2s4c_C_one_eq_A (i j : Fin 1) :
    CartanMatrix.C 1 i j = CartanMatrix.A 1 i j := by
  fin_cases i; fin_cases j; decide

private lemma ggQ2s4c_D_shift {n : ℕ} (hn : 4 ≤ n) (i j : Fin (n - 1)) :
    CartanMatrix.D n ⟨(i : ℕ) + 1, by omega⟩ ⟨(j : ℕ) + 1, by omega⟩ =
      CartanMatrix.D (n - 1) i j := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.val_mk, Fin.mk.injEq, Fin.ext_iff,
    true_and, and_true]
  split_ifs <;> omega

private lemma ggQ2s4c_D_zero_entry {n : ℕ} (hn : 4 ≤ n) (p : Fin n)
    (hp : (p : ℕ) = 0) (i j : Fin (n - 1)) :
    CartanMatrix.D n (ggQ2s4c_complEquivIf p i) (ggQ2s4c_complEquivIf p j) =
      CartanMatrix.D (n - 1) i j := by
  have h1 : ((ggQ2s4c_complEquivIf p i : Fin n)) = ⟨(i : ℕ) + 1, by omega⟩ := by
    apply Fin.ext
    rw [ggQ2s4c_complEquivIf_val]
    simp [hp]
  have h2 : ((ggQ2s4c_complEquivIf p j : Fin n)) = ⟨(j : ℕ) + 1, by omega⟩ := by
    apply Fin.ext
    rw [ggQ2s4c_complEquivIf_val]
    simp [hp]
  rw [h1, h2, ggQ2s4c_D_shift hn]

private lemma ggQ2s4c_D_fork {n : ℕ} (hn : 4 ≤ n) (p : Fin n)
    (hp : (p : ℕ) = n - 2 ∨ (p : ℕ) = n - 1) (i j : Fin (n - 1)) :
    CartanMatrix.D n (ggQ2s4c_complEquivIf p i) (ggQ2s4c_complEquivIf p j) =
      CartanMatrix.A (n - 1) i j := by
  rw [CartanMatrix.D, CartanMatrix.A]
  simp only [Matrix.of_apply, Fin.mk.injEq]
  by_cases hij : i = j
  · subst hij
    simp [ggQ2s4c_complEquivIf_val]
  · have hne : ¬ ((ggQ2s4c_complEquivIf p i : Fin n) =
        (ggQ2s4c_complEquivIf p j : Fin n)) := by
      intro hh
      exact hij ((ggQ2s4c_complEquivIf p).injective (Subtype.ext hh))
    simp only [if_neg hij, if_neg hne, ggQ2s4c_complEquivIf_val]
    split_ifs <;> omega

private lemma ggQ2s4c_D_left {n : ℕ} (hn : 4 ≤ n) (i : Fin n)
    (h1 : 1 ≤ (i : ℕ)) (h2 : (i : ℕ) + 2 < n) :
    CartanMatrix.D n i ⟨(i : ℕ) - 1, by omega⟩ = -1 := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.val_mk, Fin.mk.injEq, Fin.ext_iff,
    true_and, and_true]
  split_ifs <;> omega

private lemma ggQ2s4c_D_right {n : ℕ} (hn : 4 ≤ n) (i : Fin n)
    (h : (i : ℕ) + 3 < n) :
    CartanMatrix.D n i ⟨(i : ℕ) + 1, by omega⟩ = -1 := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.val_mk, Fin.mk.injEq, Fin.ext_iff,
    true_and, and_true]
  split_ifs <;> omega

private lemma ggQ2s4c_D_fork_n2 {n : ℕ} (hn : 4 ≤ n) :
    CartanMatrix.D n ⟨n - 3, by omega⟩ ⟨n - 2, by omega⟩ = -1 := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.val_mk, Fin.mk.injEq, Fin.ext_iff,
    true_and, and_true]
  split_ifs <;> omega

private lemma ggQ2s4c_leaf_D {n : ℕ} (hn : 4 ≤ n) (a₀ : Fin n)
    (h : ∃! c, c ≠ a₀ ∧ CartanMatrix.D n a₀ c ≠ 0) :
    (a₀ : ℕ) = 0 ∨ (a₀ : ℕ) = n - 2 ∨ (a₀ : ℕ) = n - 1 := by
  obtain ⟨c, hc, huniq⟩ := h
  by_contra hnot
  push Not at hnot
  have hi0 : 1 ≤ (a₀ : ℕ) := by omega
  have hi3 : (a₀ : ℕ) ≤ n - 3 := by omega
  have h2 : (a₀ : ℕ) + 2 < n := by omega
  let c1 : Fin n := ⟨(a₀ : ℕ) - 1, by omega⟩
  have hc1ne : c1 ≠ a₀ := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [c1, Fin.val_mk] at hv
    omega
  have hc1D : CartanMatrix.D n a₀ c1 ≠ 0 := by
    have hd := ggQ2s4c_D_left hn a₀ hi0 h2
    rw [hd]
    norm_num
  by_cases hlt : (a₀ : ℕ) + 3 < n
  · let c2 : Fin n := ⟨(a₀ : ℕ) + 1, by omega⟩
    have hc2ne : c2 ≠ a₀ := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [c2, Fin.val_mk] at hv
      omega
    have hc2D : CartanMatrix.D n a₀ c2 ≠ 0 := by
      have hd := ggQ2s4c_D_right hn a₀ hlt
      rw [hd]
      norm_num
    have hc12 : c1 ≠ c2 := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [c1, c2, Fin.val_mk] at hv
      omega
    exact hc12 ((huniq c1 ⟨hc1ne, hc1D⟩).trans (huniq c2 ⟨hc2ne, hc2D⟩).symm)
  · have hi_eq : (a₀ : ℕ) = n - 3 := by omega
    let c2 : Fin n := ⟨n - 2, by omega⟩
    have hc2ne : c2 ≠ a₀ := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [c2, Fin.val_mk] at hv
      omega
    have hc2D : CartanMatrix.D n a₀ c2 ≠ 0 := by
      have hae : a₀ = (⟨n - 3, by omega⟩ : Fin n) := Fin.ext hi_eq
      have hd := ggQ2s4c_D_fork_n2 hn
      rw [hae]
      rw [show c2 = (⟨n - 2, by omega⟩ : Fin n) from rfl]
      rw [hd]
      norm_num
    have hc12 : c1 ≠ c2 := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [c1, c2, Fin.val_mk] at hv
      omega
    exact hc12 ((huniq c1 ⟨hc1ne, hc1D⟩).trans (huniq c2 ⟨hc2ne, hc2D⟩).symm)

private theorem ggQ2s4c_D_zero_witness {n : ℕ} (hn : 4 ≤ n) (a₀ : Fin n)
    (h : (a₀ : ℕ) = 0) :
    ∃ e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀},
      ∀ i j : Fin (n - 1),
        CartanMatrix.D n (e i) (e j) = CartanMatrix.D (n - 1) i j :=
  ⟨ggQ2s4c_complEquivIf a₀, fun i j => ggQ2s4c_D_zero_entry hn a₀ h i j⟩

private theorem ggQ2s4c_D_fork_witness {n : ℕ} (hn : 4 ≤ n) (a₀ : Fin n)
    (h : (a₀ : ℕ) = n - 2 ∨ (a₀ : ℕ) = n - 1) :
    ∃ e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀},
      ∀ i j : Fin (n - 1),
        CartanMatrix.D n (e i) (e j) = CartanMatrix.A (n - 1) i j :=
  ⟨ggQ2s4c_complEquivIf a₀, fun i j => ggQ2s4c_D_fork hn a₀ h i j⟩

private lemma ggQ2s4c_D_three_perm (i j : Fin 3) :
    CartanMatrix.D 3 (Equiv.swap (0 : Fin 3) 1 i) (Equiv.swap (0 : Fin 3) 1 j) =
      CartanMatrix.A 3 i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem ggQ2s4_leaf_classical {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {n : ℕ} (e : Fin n ≃ D.ι)
    (hn : 1 ≤ n)
    (h : (∀ i j, D.cartan (e i) (e j) = CartanMatrix.A n i j) ∨
      (2 ≤ n ∧ ((∀ i j, D.cartan (e i) (e j) = CartanMatrix.B n i j) ∨
        (∀ i j, D.cartan (e i) (e j) = CartanMatrix.C n i j))) ∨
      (4 ≤ n ∧ ∀ i j, D.cartan (e i) (e j) = CartanMatrix.D n i j)) :
    D.LeafModels D.a := by
  let a₀ : Fin n := e.symm D.a
  have ha₀ : e a₀ = D.a := e.apply_symm_apply D.a
  have hleaf : ∀ {X : Matrix (Fin n) (Fin n) ℤ},
      (∀ i j, D.cartan (e i) (e j) = X i j) → ∃! c, c ≠ a₀ ∧ X a₀ c ≠ 0 := by
    intro X hX
    obtain ⟨c, hc, huniq⟩ := D.a_leaf
    refine ⟨e.symm c, ⟨?_, ?_⟩, ?_⟩
    · intro hh
      apply hc.1
      rw [← e.apply_symm_apply c, ← ha₀, hh]
    · rw [← hX a₀ (e.symm c), ha₀, e.apply_symm_apply]
      exact hc.2
    · intro y hy
      apply e.injective
      show e y = e (e.symm c)
      rw [e.apply_symm_apply]
      apply huniq (e y)
      refine ⟨?_, ?_⟩
      · intro heq
        exact hy.1 (e.injective (by rw [ha₀]; exact heq))
      · rw [← ha₀, hX a₀ y]
        exact hy.2
  rcases h with hA | hBC | hD
  · obtain ⟨c, ⟨hcne, -⟩, -⟩ := hleaf hA
    have hn2 : 2 ≤ n := by
      have h1 : 1 < Fintype.card (Fin n) :=
        Fintype.one_lt_card_iff.mpr ⟨a₀, c, fun hh => hcne hh.symm⟩
      have h1' : 1 < n := by simpa using h1
      omega
    have hle : a₀.val = 0 ∨ a₀.val = n - 1 :=
      ggQ2s4c_leaf_of_row hn2 (CartanMatrix.A n) a₀
        (fun hij => by rw [ggQ2s4c_A_prev hij]; norm_num)
        (fun hij => by rw [ggQ2s4c_A_next hij]; norm_num) (hleaf hA)
    obtain ⟨cc, hcc⟩ := ggQ2s4c_A_witness (by omega : 1 ≤ n) a₀ hle
    refine Or.inl ⟨n - 1, ggQ2s4c_equivOf D e a₀ ha₀ cc, by omega, Or.inl ?_⟩
    intro i j
    show D.cartan (↑(ggQ2s4c_equivOf D e a₀ ha₀ cc i)) _ = _
    rw [ggQ2s4c_equivOf_apply, ggQ2s4c_equivOf_apply, hA, hcc i j]
  · obtain ⟨hn2, hB | hC⟩ := hBC
    · have hle : a₀.val = 0 ∨ a₀.val = n - 1 :=
        ggQ2s4c_leaf_of_row hn2 (CartanMatrix.B n) a₀
          (fun hij => ggQ2s4c_B_prev hij) (fun hij => ggQ2s4c_B_next hij) (hleaf hB)
      rcases hle with h0 | hlast
      · by_cases hn2' : n = 2
        · subst hn2'
          obtain ⟨cc, hcc⟩ := ggQ2s4c_B_zero_witness (by omega : 1 ≤ 2) a₀ h0
          refine Or.inl ⟨1, ggQ2s4c_equivOf D e a₀ ha₀ cc, by omega, Or.inl ?_⟩
          intro i j
          show D.cartan (↑(ggQ2s4c_equivOf D e a₀ ha₀ cc i)) _ = _
          rw [ggQ2s4c_equivOf_apply, ggQ2s4c_equivOf_apply, hB, hcc i j]
          exact ggQ2s4c_B_one_eq_A i j
        · obtain ⟨cc, hcc⟩ := ggQ2s4c_B_zero_witness (by omega : 1 ≤ n) a₀ h0
          have hm2 : 2 ≤ n - 1 := by omega
          refine Or.inl ⟨n - 1, ggQ2s4c_equivOf D e a₀ ha₀ cc, by omega,
            Or.inr (Or.inl ⟨hm2, Or.inl ?_⟩)⟩
          intro i j
          show D.cartan (↑(ggQ2s4c_equivOf D e a₀ ha₀ cc i)) _ = _
          rw [ggQ2s4c_equivOf_apply, ggQ2s4c_equivOf_apply, hB, hcc i j]
      · obtain ⟨cc, hcc⟩ := ggQ2s4c_B_witness (by omega : 1 ≤ n) a₀ hlast
        refine Or.inl ⟨n - 1, ggQ2s4c_equivOf D e a₀ ha₀ cc, by omega, Or.inl ?_⟩
        intro i j
        show D.cartan (↑(ggQ2s4c_equivOf D e a₀ ha₀ cc i)) _ = _
        rw [ggQ2s4c_equivOf_apply, ggQ2s4c_equivOf_apply, hB, hcc i j]
    · have hle : a₀.val = 0 ∨ a₀.val = n - 1 :=
        ggQ2s4c_leaf_of_row hn2 (CartanMatrix.C n) a₀
          (fun hij => ggQ2s4c_C_prev hij) (fun hij => ggQ2s4c_C_next hij) (hleaf hC)
      rcases hle with h0 | hlast
      · by_cases hn2' : n = 2
        · subst hn2'
          obtain ⟨cc, hcc⟩ := ggQ2s4c_C_zero_witness (by omega : 1 ≤ 2) a₀ h0
          refine Or.inl ⟨1, ggQ2s4c_equivOf D e a₀ ha₀ cc, by omega, Or.inl ?_⟩
          intro i j
          show D.cartan (↑(ggQ2s4c_equivOf D e a₀ ha₀ cc i)) _ = _
          rw [ggQ2s4c_equivOf_apply, ggQ2s4c_equivOf_apply, hC, hcc i j]
          exact ggQ2s4c_C_one_eq_A i j
        · obtain ⟨cc, hcc⟩ := ggQ2s4c_C_zero_witness (by omega : 1 ≤ n) a₀ h0
          have hm2 : 2 ≤ n - 1 := by omega
          refine Or.inl ⟨n - 1, ggQ2s4c_equivOf D e a₀ ha₀ cc, by omega,
            Or.inr (Or.inl ⟨hm2, Or.inr ?_⟩)⟩
          intro i j
          show D.cartan (↑(ggQ2s4c_equivOf D e a₀ ha₀ cc i)) _ = _
          rw [ggQ2s4c_equivOf_apply, ggQ2s4c_equivOf_apply, hC, hcc i j]
      · obtain ⟨cc, hcc⟩ := ggQ2s4c_C_witness (by omega : 1 ≤ n) a₀ hlast
        refine Or.inl ⟨n - 1, ggQ2s4c_equivOf D e a₀ ha₀ cc, by omega, Or.inl ?_⟩
        intro i j
        show D.cartan (↑(ggQ2s4c_equivOf D e a₀ ha₀ cc i)) _ = _
        rw [ggQ2s4c_equivOf_apply, ggQ2s4c_equivOf_apply, hC, hcc i j]
  · obtain ⟨hn4, hD⟩ := hD
    have hle : (a₀ : ℕ) = 0 ∨ (a₀ : ℕ) = n - 2 ∨ (a₀ : ℕ) = n - 1 :=
      ggQ2s4c_leaf_D hn4 a₀ (hleaf hD)
    rcases hle with h0 | hfork | hlast
    · by_cases hn4' : n = 4
      · subst hn4'
        obtain ⟨cc, hcc⟩ := ggQ2s4c_D_zero_witness (by omega : 4 ≤ 4) a₀ h0
        refine Or.inl ⟨3, ggQ2s4c_equivOf D e a₀ ha₀
          ((Equiv.swap (0 : Fin 3) 1).trans cc), by omega, Or.inl ?_⟩
        intro i j
        show D.cartan
          (↑(ggQ2s4c_equivOf D e a₀ ha₀ ((Equiv.swap (0 : Fin 3) 1).trans cc) i)) _ = _
        rw [ggQ2s4c_equivOf_apply, ggQ2s4c_equivOf_apply, hD]
        change CartanMatrix.D 4 ↑(cc (Equiv.swap (0 : Fin 3) 1 i))
          ↑(cc (Equiv.swap (0 : Fin 3) 1 j)) = CartanMatrix.A 3 i j
        rw [hcc]
        exact ggQ2s4c_D_three_perm i j
      · obtain ⟨cc, hcc⟩ := ggQ2s4c_D_zero_witness hn4 a₀ h0
        have hm4 : 4 ≤ n - 1 := by omega
        refine Or.inl ⟨n - 1, ggQ2s4c_equivOf D e a₀ ha₀ cc, by omega,
          Or.inr (Or.inr ⟨hm4, ?_⟩)⟩
        intro i j
        show D.cartan (↑(ggQ2s4c_equivOf D e a₀ ha₀ cc i)) _ = _
        rw [ggQ2s4c_equivOf_apply, ggQ2s4c_equivOf_apply, hD, hcc i j]
    · obtain ⟨cc, hcc⟩ := ggQ2s4c_D_fork_witness hn4 a₀ (Or.inl hfork)
      refine Or.inl ⟨n - 1, ggQ2s4c_equivOf D e a₀ ha₀ cc, by omega, Or.inl ?_⟩
      intro i j
      show D.cartan (↑(ggQ2s4c_equivOf D e a₀ ha₀ cc i)) _ = _
      rw [ggQ2s4c_equivOf_apply, ggQ2s4c_equivOf_apply, hD, hcc i j]
    · obtain ⟨cc, hcc⟩ := ggQ2s4c_D_fork_witness hn4 a₀ (Or.inr hlast)
      refine Or.inl ⟨n - 1, ggQ2s4c_equivOf D e a₀ ha₀ cc, by omega, Or.inl ?_⟩
      intro i j
      show D.cartan (↑(ggQ2s4c_equivOf D e a₀ ha₀ cc i)) _ = _
      rw [ggQ2s4c_equivOf_apply, ggQ2s4c_equivOf_apply, hD, hcc i j]

end CFSG.StandardType

end

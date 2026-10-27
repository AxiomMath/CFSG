module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs

public section

namespace CFSG.StandardType

open Module

private lemma ggQ2sa_A_self (n : ℕ) (i : Fin n) : CartanMatrix.A n i i = 2 := by
  simp [CartanMatrix.A]

private lemma ggQ2sa_A_adj (n : ℕ) {i j : Fin n} (hne : i ≠ j)
    (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) : CartanMatrix.A n i j = -1 := by
  simp only [CartanMatrix.A, Matrix.of_apply, if_neg hne, if_pos h]

private lemma ggQ2sa_A_other (n : ℕ) {i j : Fin n} (hne : i ≠ j)
    (h1 : i.val + 1 ≠ j.val) (h2 : j.val + 1 ≠ i.val) : CartanMatrix.A n i j = 0 := by
  simp only [CartanMatrix.A, Matrix.of_apply, if_neg hne,
    if_neg (show ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) from fun h => h.elim h1 h2)]

private lemma ggQ2sa_classify (m : ℕ) (hm : 3 ≤ m)
    (π' : Equiv.Perm (Fin m)) (μ' : Fin m → ZMod 3) (hμ : ∀ i, μ' i ≠ 0)
    (hcomp : ∀ i j : Fin m,
      μ' i * (CartanMatrix.A m i j : ZMod 3) =
        μ' j * (CartanMatrix.A m (π' i) (π' j) : ZMod 3)) :
    (∃ c : ZMod 3, ∀ i : Fin m, μ' i = c) ∧
      ((∀ i : Fin m, π' i = i) ∨ (∀ i : Fin m, (π' i).val + i.val = m - 1)) := by
  have hadj : ∀ i j : Fin m, i.val + 1 = j.val ∨ j.val + 1 = i.val →
      (π' i).val + 1 = (π' j).val ∨ (π' j).val + 1 = (π' i).val := by
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      rcases hij with h | h <;> omega
    have hA : CartanMatrix.A m i j = -1 := ggQ2sa_A_adj m hne hij
    have hAc : ((CartanMatrix.A m i j : ℤ) : ZMod 3) = -1 := by rw [hA]; exact Int.cast_negSucc 0
    have hpne : π' i ≠ π' j := fun hh => hne (π'.injective hh)
    by_contra hcon
    have h1 : (π' i).val + 1 ≠ (π' j).val := fun hh => hcon (Or.inl hh)
    have h2 : (π' j).val + 1 ≠ (π' i).val := fun hh => hcon (Or.inr hh)
    have h0 : CartanMatrix.A m (π' i) (π' j) = 0 := ggQ2sa_A_other m hpne h1 h2
    have h0c : ((CartanMatrix.A m (π' i) (π' j) : ℤ) : ZMod 3) = 0 := by rw [h0]; norm_num
    have hc := hcomp i j
    rw [hAc, h0c] at hc
    have hc1 : μ' i * (-1 : ZMod 3) = 0 := by simpa only [mul_zero] using hc
    have hz : μ' i = 0 := by
      refine mul_right_cancel₀ (by decide : (-1 : ZMod 3) ≠ 0) ?_
      rw [hc1, zero_mul]
    exact hμ i hz
  have hedge : ∀ i j : Fin m, i.val + 1 = j.val ∨ j.val + 1 = i.val → μ' i = μ' j := by
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      rcases hij with h | h <;> omega
    have hpne : π' i ≠ π' j := fun hh => hne (π'.injective hh)
    have hA : CartanMatrix.A m i j = -1 := ggQ2sa_A_adj m hne hij
    have hA' : CartanMatrix.A m (π' i) (π' j) = -1 := ggQ2sa_A_adj m hpne (hadj i j hij)
    have hAc : ((CartanMatrix.A m i j : ℤ) : ZMod 3) = -1 := by rw [hA]; exact Int.cast_negSucc 0
    have hA'c : ((CartanMatrix.A m (π' i) (π' j) : ℤ) : ZMod 3) = -1 := by
      rw [hA']; exact Int.cast_negSucc 0
    have hc := hcomp i j
    rw [hAc, hA'c] at hc
    have hneg : (-1 : ZMod 3) ≠ 0 := by decide
    exact mul_right_cancel₀ hneg hc
  let wv : ℕ → ZMod 3 := fun n => if h : n < m then μ' ⟨n, h⟩ else 0
  have hwv : ∀ n (h : n < m), wv n = μ' ⟨n, h⟩ := by
    intro n h
    dsimp only [wv]
    rw [dif_pos h]
  have hwconst : ∀ n, n < m → wv n = wv 0 := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hk' : k < m := Nat.lt_of_succ_lt hk
      have hedge' : μ' ⟨k, hk'⟩ = μ' ⟨k + 1, hk⟩ :=
        hedge ⟨k, hk'⟩ ⟨k + 1, hk⟩ (Or.inl rfl)
      rw [hwv (k + 1) hk, ← hedge', ← hwv k hk']
      exact ih hk'
  have hmuconst : ∃ c : ZMod 3, ∀ i : Fin m, μ' i = c := by
    refine ⟨μ' ⟨0, by omega⟩, ?_⟩
    intro i
    have := hwconst i.val i.isLt
    rw [hwv i.val i.isLt, hwv 0 (by omega)] at this
    simpa using this
  let v : ℕ → ℕ := fun n => if h : n < m then (π' ⟨n, h⟩).val else 0
  have hvv : ∀ n (h : n < m), v n = (π' ⟨n, h⟩).val := by
    intro n h
    dsimp only [v]
    rw [dif_pos h]
  have hinjv : ∀ {a b : ℕ}, a < m → b < m → v a = v b → a = b := by
    intro a b ha hb hab
    have h2 : (π' ⟨a, ha⟩).val = (π' ⟨b, hb⟩).val := by
      rw [← hvv a ha, ← hvv b hb, hab]
    have h4 := π'.injective (Fin.ext h2)
    have := congrArg Fin.val h4
    simpa using this
  have hdir : ∀ n, n + 1 < m → v n + 1 = v (n + 1) ∨ v (n + 1) + 1 = v n := by
    intro n hn
    have hn' : n < m := by omega
    have h := hadj ⟨n, hn'⟩ ⟨n + 1, hn⟩ (Or.inl rfl)
    simpa [hvv n hn', hvv (n + 1) hn] using h
  have hdir_pos : v 0 + 1 = v 1 → ∀ n, n + 1 < m → v n + 1 = v (n + 1) := by
    intro hbase n
    induction n with
    | zero => intro _; exact hbase
    | succ k ih =>
      intro hk
      have hk1 : k + 1 < m := by omega
      have hprev : v k + 1 = v (k + 1) := ih hk1
      rcases hdir (k + 1) hk with h | h
      · exact h
      · exfalso
        have hcontra : v ((k + 1) + 1) = v k := by omega
        have hcon := hinjv (a := (k + 1) + 1) (b := k) (by omega) (by omega) hcontra
        omega
  have hdir_neg : v 1 + 1 = v 0 → ∀ n, n + 1 < m → v (n + 1) + 1 = v n := by
    intro hbase n
    induction n with
    | zero => intro _; exact hbase
    | succ k ih =>
      intro hk
      have hk1 : k + 1 < m := by omega
      have hprev : v (k + 1) + 1 = v k := ih hk1
      rcases hdir (k + 1) hk with h | h
      · exfalso
        have hcontra : v ((k + 1) + 1) = v k := by omega
        have hcon := hinjv (a := (k + 1) + 1) (b := k) (by omega) (by omega) hcontra
        omega
      · exact h
  have hsum_pos : v 0 + 1 = v 1 → ∀ n, n < m → v n = v 0 + n := by
    intro hbase n
    induction n with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk1 : k < m := by omega
      have hstep : v k + 1 = v (k + 1) := hdir_pos hbase k (by omega)
      rw [← hstep, ih hk1]
      omega
  have hsum_neg : v 1 + 1 = v 0 → ∀ n, n < m → v n + n = v 0 := by
    intro hbase n
    induction n with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk1 : k < m := by omega
      have hstep : v (k + 1) + 1 = v k := hdir_neg hbase k (by omega)
      have hk_eq : v (k + 1) + (k + 1) = v k + k := by omega
      rw [hk_eq, ih hk1]
  have hdich : (∀ i : Fin m, π' i = i) ∨
      (∀ i : Fin m, (π' i).val + i.val = m - 1) := by
    rcases hdir 0 (by omega) with h01 | h01
    · left
      have hbase : v 0 + 1 = v 1 := by simpa using h01
      have hform := hsum_pos hbase
      intro i
      apply Fin.ext
      have hi := hform i.val i.isLt
      have hlast := hform (m - 1) (by omega)
      have hvm : v (m - 1) ≤ m - 1 := by
        rw [hvv (m - 1) (by omega)]
        have := (π' ⟨m - 1, by omega⟩).isLt
        omega
      have hv0 : v 0 = 0 := by omega
      rw [← hvv i i.isLt]
      omega
    · right
      have hbase : v 1 + 1 = v 0 := by simpa using h01
      have hform := hsum_neg hbase
      intro i
      have hi := hform i.val i.isLt
      have hlast := hform (m - 1) (by omega)
      have hv0le : v 0 ≤ m - 1 := by
        rw [hvv 0 (by omega)]
        have := (π' ⟨0, by omega⟩).isLt
        omega
      have hv0 : v 0 = m - 1 := by omega
      rw [← hvv i i.isLt]
      omega
  exact ⟨hmuconst, hdich⟩

private noncomputable def ggQ2sa_R (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a})
    (n : ℕ) : D.V ≃ₗ[ZMod 3] D.V :=
  if h : n < m then D.simpleRefl (f ⟨n, h⟩) else 1

private noncomputable def ggQ2sa_H (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a})
    (n : ℕ) : D.V :=
  if h : n < m then D.coroot (f ⟨n, h⟩) else 0

private def ggQ2sa_Ac (m : ℕ) (k j : ℕ) : ZMod 3 :=
  if hk : k < m then if hj : j < m then (CartanMatrix.A m ⟨k, hk⟩ ⟨j, hj⟩ : ZMod 3) else 0
  else 0

private lemma ggQ2sa_Ac_pos (m : ℕ) {k j : ℕ} (hk : k < m) (hj : j < m) :
    ggQ2sa_Ac m k j = ((CartanMatrix.A m ⟨k, hk⟩ ⟨j, hj⟩ : ℤ) : ZMod 3) := by
  simp [ggQ2sa_Ac, dif_pos hk, dif_pos hj]

private lemma ggQ2sa_R_H (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.A m i j)
    {n i : ℕ} (hn : n < m) (hi : i < m) :
    ggQ2sa_R D f n (ggQ2sa_H D f i) = ggQ2sa_H D f i - ggQ2sa_Ac m n i • ggQ2sa_H D f n := by
  simp only [ggQ2sa_R, ggQ2sa_H, ggQ2sa_Ac, dif_pos hn, dif_pos hi, GGQ2Lin.simpleRefl,
    Module.reflection_apply, D.pairing, hf]

private lemma ggQ2sa_R_H_fixed (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.A m i j)
    {n j : ℕ} (hn : n < m) (hj : j < m) (hne : n ≠ j) (h1 : n + 1 ≠ j)
    (h2 : j + 1 ≠ n) :
    ggQ2sa_R D f n (ggQ2sa_H D f j) = ggQ2sa_H D f j := by
  have hne' : (⟨n, hn⟩ : Fin m) ≠ ⟨j, hj⟩ := fun h => hne (by simpa using congrArg Fin.val h)
  have h1' : (⟨n, hn⟩ : Fin m).val + 1 ≠ (⟨j, hj⟩ : Fin m).val := by simpa using h1
  have h2' : (⟨j, hj⟩ : Fin m).val + 1 ≠ (⟨n, hn⟩ : Fin m).val := by simpa using h2
  have hAc : ggQ2sa_Ac m n j = 0 := by
    rw [ggQ2sa_Ac_pos m hn hj, ggQ2sa_A_other m hne' h1' h2']
    exact Int.cast_zero
  rw [ggQ2sa_R_H D f hf hn hj, hAc, zero_smul, sub_zero]

private noncomputable def ggQ2sa_T (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a}) :
    ℕ → D.V ≃ₗ[ZMod 3] D.V
  | 0 => 1
  | k + 1 => ggQ2sa_R D f k * ggQ2sa_T D f k

private noncomputable def ggQ2sa_W (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a}) :
    ℕ → D.V ≃ₗ[ZMod 3] D.V
  | 0 => 1
  | k + 1 => ggQ2sa_W D f k * ggQ2sa_T D f (k + 1)

private lemma ggQ2sa_T_zero (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a}) :
    ggQ2sa_T D f 0 = 1 := rfl
private lemma ggQ2sa_T_succ (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a}) (k : ℕ) :
    ggQ2sa_T D f (k + 1) = ggQ2sa_R D f k * ggQ2sa_T D f k := rfl
private lemma ggQ2sa_W_zero (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a}) :
    ggQ2sa_W D f 0 = 1 := rfl
private lemma ggQ2sa_W_succ (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a}) (k : ℕ) :
    ggQ2sa_W D f (k + 1) = ggQ2sa_W D f k * ggQ2sa_T D f (k + 1) := rfl

private lemma ggQ2sa_R_sum_range (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.A m i j)
    {k : ℕ} (hk : k < m) (hk1 : 1 ≤ k) :
    (∑ j ∈ Finset.range k, ggQ2sa_R D f k (ggQ2sa_H D f j)) =
      ∑ j ∈ Finset.range (k + 1), ggQ2sa_H D f j := by
  have hk_eq : k = (k - 1) + 1 := by omega
  have hkm1 : k - 1 < m := by omega
  have hsum : (∑ j ∈ Finset.range k, ggQ2sa_R D f k (ggQ2sa_H D f j)) =
      (∑ j ∈ Finset.range (k - 1), ggQ2sa_R D f k (ggQ2sa_H D f j)) +
        ggQ2sa_R D f k (ggQ2sa_H D f (k - 1)) := by
    rw [congrArg Finset.range hk_eq]
    exact Finset.sum_range_succ _ _
  have hfirst : (∑ j ∈ Finset.range (k - 1), ggQ2sa_R D f k (ggQ2sa_H D f j)) =
      ∑ j ∈ Finset.range (k - 1), ggQ2sa_H D f j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjlt : j < k - 1 := Finset.mem_range.mp hj
    have hjm : j < m := by omega
    exact ggQ2sa_R_H_fixed D f hf hk hjm (by omega) (by omega) (by omega)
  have hlast : ggQ2sa_R D f k (ggQ2sa_H D f (k - 1)) =
      ggQ2sa_H D f (k - 1) + ggQ2sa_H D f k := by
    rw [ggQ2sa_R_H D f hf hk hkm1]
    have hne : (⟨k, hk⟩ : Fin m) ≠ (⟨k - 1, hkm1⟩ : Fin m) := by
      intro h
      have hval : k = k - 1 := by simpa using congrArg Fin.val h
      omega
    have hadj : (⟨k, hk⟩ : Fin m).val + 1 = (⟨k - 1, hkm1⟩ : Fin m).val ∨
        (⟨k - 1, hkm1⟩ : Fin m).val + 1 = (⟨k, hk⟩ : Fin m).val :=
      Or.inr (by simp only [Fin.val_mk]; omega)
    have hAc : ggQ2sa_Ac m k (k - 1) = -1 := by
      rw [ggQ2sa_Ac_pos m hk hkm1, ggQ2sa_A_adj m hne hadj]
      exact Int.cast_negSucc 0
    rw [hAc]
    rw [show (-1 : ZMod 3) • ggQ2sa_H D f k = - ggQ2sa_H D f k from
      neg_one_smul (ZMod 3) (ggQ2sa_H D f k)]
    abel
  have e1 : (∑ j ∈ Finset.range (k + 1), ggQ2sa_H D f j) =
      (∑ j ∈ Finset.range k, ggQ2sa_H D f j) + ggQ2sa_H D f k :=
    Finset.sum_range_succ _ _
  have e2 : (∑ j ∈ Finset.range k, ggQ2sa_H D f j) =
      (∑ j ∈ Finset.range (k - 1), ggQ2sa_H D f j) + ggQ2sa_H D f (k - 1) := by
    rw [congrArg Finset.range hk_eq]
    exact Finset.sum_range_succ _ _
  rw [hsum, hfirst, hlast, e1, e2]
  abel

private lemma ggQ2sa_T_facts (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.A m i j) :
    ∀ k, k ≤ m →
      (∀ j, j + 1 < k → ggQ2sa_T D f k (ggQ2sa_H D f (j + 1)) = ggQ2sa_H D f j) ∧
      (1 ≤ k → ggQ2sa_T D f k (ggQ2sa_H D f 0) =
        - ∑ j ∈ Finset.range k, ggQ2sa_H D f j) ∧
      (∀ j, k + 1 ≤ j → j < m → ggQ2sa_T D f k (ggQ2sa_H D f j) = ggQ2sa_H D f j) ∧
      (1 ≤ k → k < m → ggQ2sa_T D f k (ggQ2sa_H D f k) =
        ggQ2sa_H D f k + ggQ2sa_H D f (k - 1)) := by
  intro k0
  induction k0 with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj; omega
    · intro h; omega
    · intro j hj hjm
      rfl
    · intro h; omega
  | succ k ih =>
    intro hk
    have hk' : k ≤ m := by omega
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih hk'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj
      have hjlt : j < k := by omega
      have hjltm : j < m := by omega
      rw [ggQ2sa_T_succ, LinearEquiv.mul_apply]
      by_cases hjk : j + 1 = k
      · have hj_eq : j = k - 1 := by omega
        rw [hj_eq]
        have hk_sub : k - 1 + 1 = k := by omega
        rw [hk_sub]
        have hkm : k < m := by omega
        have hkm1 : k - 1 < m := by omega
        rw [ih4 (by omega) hkm, map_add]
        have h1 : ggQ2sa_R D f k (ggQ2sa_H D f k) = - ggQ2sa_H D f k := by
          rw [ggQ2sa_R_H D f hf hkm hkm]
          have hAc : ggQ2sa_Ac m k k = 2 := by
            rw [ggQ2sa_Ac_pos m hkm hkm, ggQ2sa_A_self]
            norm_num
          rw [hAc]
          rw [show (2 : ZMod 3) • ggQ2sa_H D f k =
              ggQ2sa_H D f k + ggQ2sa_H D f k from by
            rw [show (2 : ZMod 3) = 1 + 1 by norm_num, add_smul, one_smul]]
          abel
        have h2 : ggQ2sa_R D f k (ggQ2sa_H D f (k - 1)) =
            ggQ2sa_H D f (k - 1) + ggQ2sa_H D f k := by
          rw [ggQ2sa_R_H D f hf hkm hkm1]
          have hne : (⟨k, hkm⟩ : Fin m) ≠ (⟨k - 1, hkm1⟩ : Fin m) := by
            intro h
            have hval : k = k - 1 := by simpa using congrArg Fin.val h
            omega
          have hAc : ggQ2sa_Ac m k (k - 1) = -1 := by
            rw [ggQ2sa_Ac_pos m hkm hkm1,
              ggQ2sa_A_adj m hne (Or.inr (by simp only [Fin.val_mk]; omega))]
            exact Int.cast_negSucc 0
          rw [hAc]
          rw [show (-1 : ZMod 3) • ggQ2sa_H D f k = - ggQ2sa_H D f k from
            neg_one_smul (ZMod 3) (ggQ2sa_H D f k)]
          abel
        rw [h1, h2]
        abel
      · rw [ih1 j (by omega)]
        exact ggQ2sa_R_H_fixed D f hf (by omega) hjltm (by omega) (by omega) (by omega)
    · intro hk1
      rw [ggQ2sa_T_succ, LinearEquiv.mul_apply]
      by_cases hk0 : k = 0
      · subst hk0
        change ggQ2sa_R D f 0 (ggQ2sa_T D f 0 (ggQ2sa_H D f 0)) =
          - ∑ j ∈ Finset.range 1, ggQ2sa_H D f j
        rw [ggQ2sa_T_zero]
        change ggQ2sa_R D f 0 (ggQ2sa_H D f 0) = - ∑ j ∈ Finset.range 1, ggQ2sa_H D f j
        rw [ggQ2sa_R_H D f hf (by omega) (by omega)]
        have hAc : ggQ2sa_Ac m 0 0 = 2 := by
          rw [ggQ2sa_Ac_pos m (by omega) (by omega), ggQ2sa_A_self]
          norm_num
        rw [hAc, Finset.sum_range_one]
        rw [show (2 : ZMod 3) • ggQ2sa_H D f 0 =
            ggQ2sa_H D f 0 + ggQ2sa_H D f 0 from by
          rw [show (2 : ZMod 3) = 1 + 1 by norm_num, add_smul, one_smul]]
        abel
      · rw [ih2 (by omega), map_neg, map_sum]
        exact congrArg Neg.neg (ggQ2sa_R_sum_range D f hf (by omega) (by omega))
    · intro j hj hjm
      rw [ggQ2sa_T_succ, LinearEquiv.mul_apply, ih3 j (by omega) hjm]
      exact ggQ2sa_R_H_fixed D f hf (by omega) hjm (by omega) (by omega) (by omega)
    · intro hk1 hkm
      rw [ggQ2sa_T_succ, LinearEquiv.mul_apply, ih3 (k + 1) (by omega) hkm]
      rw [ggQ2sa_R_H D f hf (by omega) hkm]
      have hne : (⟨k, by omega⟩ : Fin m) ≠ (⟨k + 1, hkm⟩ : Fin m) := by
        intro h
        have hval : k = k + 1 := by simpa using congrArg Fin.val h
        omega
      have hAc : ggQ2sa_Ac m k (k + 1) = -1 := by
        rw [ggQ2sa_Ac_pos m (by omega) hkm,
          ggQ2sa_A_adj m hne (Or.inl (by simp only [Fin.val_mk]))]
        exact Int.cast_negSucc 0
      rw [hAc]
      rw [show (-1 : ZMod 3) • ggQ2sa_H D f k = - ggQ2sa_H D f k from
        neg_one_smul (ZMod 3) (ggQ2sa_H D f k)]
      abel

private lemma ggQ2sa_W_facts (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.A m i j) :
    ∀ k, k ≤ m →
      (∀ i, i < k → ggQ2sa_W D f k (ggQ2sa_H D f i) = - ggQ2sa_H D f (k - 1 - i)) ∧
      (k < m → ggQ2sa_W D f k (ggQ2sa_H D f k) =
        ∑ j ∈ Finset.range (k + 1), ggQ2sa_H D f j) ∧
      (∀ j, k + 1 ≤ j → j < m → ggQ2sa_W D f k (ggQ2sa_H D f j) = ggQ2sa_H D f j) := by
  intro k0
  induction k0 with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_⟩
    · intro i hi; omega
    · intro _
      rw [ggQ2sa_W_zero, Finset.sum_range_one]
      rfl
    · intro j hj hjm
      rfl
  | succ k ih =>
    intro hk
    have hk' : k ≤ m := by omega
    obtain ⟨ih1, ih2, ih3⟩ := ih hk'
    obtain ⟨tf1, tf2, tf3, tf4⟩ := ggQ2sa_T_facts D f hf (k + 1) hk
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rw [ggQ2sa_W_succ, LinearEquiv.mul_apply]
      by_cases hi0 : i = 0
      · subst hi0
        rw [tf2 (by omega), map_neg, map_sum]
        have hWsum : (∑ j ∈ Finset.range (k + 1), ggQ2sa_W D f k (ggQ2sa_H D f j)) =
            ggQ2sa_H D f k := by
          rw [Finset.sum_range_succ]
          have hfirst : (∑ j ∈ Finset.range k, ggQ2sa_W D f k (ggQ2sa_H D f j)) =
              ∑ j ∈ Finset.range k, - ggQ2sa_H D f (k - 1 - j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            exact ih1 j (Finset.mem_range.mp hj)
          rw [hfirst, Finset.sum_neg_distrib, ih2 (by omega), Finset.sum_range_reflect,
            Finset.sum_range_succ]
          abel
        rw [hWsum]
        rfl
      · have hi_eq : i = (i - 1) + 1 := by omega
        rw [hi_eq, tf1 (i - 1) (by omega), ih1 (i - 1) (by omega)]
        rw [show k - 1 - (i - 1) = k + 1 - 1 - (i - 1 + 1) by omega]
    · intro hkm
      rw [ggQ2sa_W_succ, LinearEquiv.mul_apply, tf4 (by omega) hkm]
      rw [show k + 1 - 1 = k by omega]
      rw [map_add, ih3 (k + 1) (by omega) hkm, ih2 (by omega)]
      rw [Finset.sum_range_succ (f := ggQ2sa_H D f) (n := k + 1)]
      abel
    · intro j hj hjm
      rw [ggQ2sa_W_succ, LinearEquiv.mul_apply, tf3 j (by omega) hjm]
      exact ih3 j (by omega) hjm

private lemma ggQ2sa_R_mem (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a}) (n : ℕ) :
    ggQ2sa_R D f n ∈ D.parab {k | k ≠ D.a} := by
  rw [ggQ2sa_R]
  by_cases hn : n < m
  · rw [dif_pos hn]
    exact Subgroup.subset_closure ⟨f ⟨n, hn⟩, (f ⟨n, hn⟩).2, rfl⟩
  · rw [dif_neg hn]
    exact Subgroup.one_mem _

private lemma ggQ2sa_T_mem (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a}) :
    ∀ k, ggQ2sa_T D f k ∈ D.parab {k | k ≠ D.a} := by
  intro k
  induction k with
  | zero => rw [ggQ2sa_T_zero]; exact Subgroup.one_mem _
  | succ k ih => rw [ggQ2sa_T_succ]; exact Subgroup.mul_mem _ (ggQ2sa_R_mem D f k) ih

private lemma ggQ2sa_W_mem (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a}) :
    ∀ k, ggQ2sa_W D f k ∈ D.parab {k | k ≠ D.a} := by
  intro k
  induction k with
  | zero => rw [ggQ2sa_W_zero]; exact Subgroup.one_mem _
  | succ k ih =>
      rw [ggQ2sa_W_succ]
      exact Subgroup.mul_mem _ ih (ggQ2sa_T_mem D f (k + 1))

private lemma ggQ2sa_W_coroot (D : GGQ2Lin 3) {m : ℕ} (f : Fin m ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.A m i j) (i : Fin m) :
    ggQ2sa_W D f m (D.coroot (f i)) = - D.coroot (f ⟨m - 1 - i.val, by omega⟩) := by
  have h := (ggQ2sa_W_facts D f hf m le_rfl).1 i.val i.isLt
  rw [ggQ2sa_H, dif_pos i.isLt] at h
  rw [Fin.eta] at h
  rw [ggQ2sa_H, dif_pos (by omega)] at h
  exact h

private lemma ggQ2sa_smul_neg_neg (D : GGQ2Lin 3) (c : ZMod 3) (x : D.V) :
    c • x = (-c) • (-x) := by
  rw [smul_neg]
  rw [show (-c : ZMod 3) • x = -(c • x) from neg_smul c x, neg_neg]

theorem ggQ2s5_of_A (D : GGQ2Lin 3) {m : ℕ} (hm : 3 ≤ m) (f : Fin m ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.A m i j)
    {π : {k // k ≠ D.a} ≃ {k // k ≠ D.a}} {μ : {k // k ≠ D.a} → ZMod 3}
    (h : D.ScaledAut D.a π μ) : D.ScalarModW D.a π μ := by
  haveI : NeZero m := ⟨by omega⟩
  let π' : Equiv.Perm (Fin m) := (f.trans π).trans f.symm
  let μ' : Fin m → ZMod 3 := fun i => μ (f i)
  have hμ' : ∀ i : Fin m, μ' i ≠ 0 := fun i => h.1 (f i)
  have hπ' : ∀ i : Fin m, π (f i) = f (π' i) := by
    intro i
    change π (f i) = f (f.symm (π (f i)))
    rw [Equiv.apply_symm_apply]
  have hcomp : ∀ i j : Fin m,
      μ' i * (CartanMatrix.A m i j : ZMod 3) =
        μ' j * (CartanMatrix.A m (π' i) (π' j) : ZMod 3) := by
    intro i j
    have hc := h.2 (f i) (f j)
    rw [hf i j, hπ' i, hπ' j, hf] at hc
    exact hc
  obtain ⟨⟨c, hc⟩, hdich⟩ := ggQ2sa_classify m hm π' μ' hμ' hcomp
  have hcne : c ≠ 0 := fun hc0 => hμ' 0 (by rw [hc 0, hc0])
  have hcval : c = 1 ∨ c = -1 :=
    (by decide : ∀ d : ZMod 3, d ≠ 0 → d = 1 ∨ d = -1) c hcne
  rcases hdich with hid | hrev
  · refine ⟨c, hcval, 1, Subgroup.one_mem _, ?_⟩
    intro i
    have hμi : μ i = c := by
      have := hc (f.symm i)
      change μ (f (f.symm i)) = c at this
      rwa [show f (f.symm i) = i from Equiv.apply_symm_apply f i] at this
    have hπi : π i = i := by
      have h1 := hπ' (f.symm i)
      rw [show f (f.symm i) = i from Equiv.apply_symm_apply f i,
        hid (f.symm i), Equiv.apply_symm_apply] at h1
      exact h1
    rw [hμi, hπi]
    rfl
  · refine ⟨-c, ?_, ggQ2sa_W D f m, ggQ2sa_W_mem D f m, ?_⟩
    · rcases hcval with h | h
      · right; rw [h]
      · left; rw [h]; decide
    · intro i
      let j : Fin m := f.symm i
      have hfj : f j = i := f.apply_symm_apply i
      have hμi : μ i = c := by
        have := hc j
        change μ (f j) = c at this
        rwa [hfj] at this
      have hπi : π i = f (π' j) := by
        have := hπ' j
        rwa [hfj] at this
      have hrevj : π' j = ⟨m - 1 - j.val, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_mk]
        have := hrev j
        omega
      have hWj : ggQ2sa_W D f m (D.coroot (f j)) = - D.coroot (f (π' j)) := by
        have h := ggQ2sa_W_coroot D f hf j
        rw [← hrevj] at h
        exact h
      rw [hμi, hπi, ← hfj, hWj]
      exact ggQ2sa_smul_neg_neg D c (D.coroot (f (π' j)))

end CFSG.StandardType

end




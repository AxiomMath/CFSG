module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private def ggQ2xCT_pred {m : ℕ} (p : Fin m) : Fin m :=
  ⟨(p : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) p.isLt⟩

private def ggQ2xCT_succ {m : ℕ} (p : Fin m) (h : (p : ℕ) + 1 < m) : Fin m :=
  ⟨(p : ℕ) + 1, h⟩

private def ggQ2xCT_Acoef {m : ℕ} (p q : Fin m) : ZMod 3 :=
  if p = q then 2 else if (p : ℕ) + 1 = (q : ℕ) ∨ (q : ℕ) + 1 = (p : ℕ) then 2 else 0

private theorem ggQ2xCT_rec (N : ℕ) (d : ℕ → ZMod 3)
    (h0 : 2 * d 0 = d 1)
    (hstep : ∀ k, 1 ≤ k → k + 1 < N → d (k + 1) + d (k - 1) = 2 * d k) :
    ∀ k, k < N → d k = ((k + 1 : ℕ) : ZMod 3) * d 0 := by
  intro k
  refine Nat.strong_induction_on k (fun k ih => ?_)
  intro hk
  match k with
  | 0 => simp
  | 1 => rw [← h0]; norm_num
  | j + 2 =>
    have h1 : 1 ≤ j + 1 := by omega
    have hlt : j + 1 + 1 < N := by omega
    have hs : d (j + 2) + d j = 2 * d (j + 1) := by
      simpa only [Nat.add_sub_cancel] using hstep (j + 1) h1 hlt
    rw [ih (j + 1) (by omega) (by omega), ih j (by omega) (by omega)] at hs
    have hcancel : d (j + 2) + ((j + 1 : ℕ) : ZMod 3) * d 0
        = ((j + 3 : ℕ) : ZMod 3) * d 0 + ((j + 1 : ℕ) : ZMod 3) * d 0 := by
      rw [hs]
      push_cast
      ring_nf
    exact add_right_cancel hcancel

private theorem ggQ2xCT_sum_eq_of_lt {m : ℕ} (f : Fin m → ZMod 3) {a : ℕ} (ha : a < m) :
    (∑ q : Fin m, (if a = (q : ℕ) then f q else 0)) = f ⟨a, ha⟩ := by
  rw [Finset.sum_eq_single (⟨a, ha⟩ : Fin m)]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext h.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem ggQ2xCT_sum_succ {m : ℕ} (f : Fin m → ZMod 3) (p : Fin m) :
    (∑ q : Fin m, (if (p : ℕ) + 1 = (q : ℕ) then f q else 0))
      = if h : (p : ℕ) + 1 < m then f (ggQ2xCT_succ p h) else 0 := by
  by_cases h : (p : ℕ) + 1 < m
  · rw [dif_pos h, ggQ2xCT_sum_eq_of_lt f h]
    rfl
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    intro hh
    exact h (hh.symm ▸ q.isLt)

private theorem ggQ2xCT_sum_pred {m : ℕ} (f : Fin m → ZMod 3) (p : Fin m) :
    (∑ q : Fin m, (if (q : ℕ) + 1 = (p : ℕ) then f q else 0))
      = if h : 0 < (p : ℕ) then f (ggQ2xCT_pred p) else 0 := by
  by_cases h : 0 < (p : ℕ)
  · rw [dif_pos h]
    have ha : (p : ℕ) - 1 < m := Nat.lt_of_le_of_lt (Nat.sub_le _ _) p.isLt
    have hcongr : (∑ q : Fin m, (if (q : ℕ) + 1 = (p : ℕ) then f q else 0))
        = ∑ q : Fin m, (if (p : ℕ) - 1 = (q : ℕ) then f q else 0) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [if_congr (by omega : ((q : ℕ) + 1 = (p : ℕ)) ↔ ((p : ℕ) - 1 = (q : ℕ))) rfl rfl]
    rw [hcongr, ggQ2xCT_sum_eq_of_lt f ha]
    rfl
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    omega

private theorem ggQ2xCT_coefA {m : ℕ} (p q : Fin m) :
    ((CartanMatrix.A m p q : ℤ) : ZMod 3) = ggQ2xCT_Acoef p q := by
  by_cases hpq : p = q
  · subst hpq
    have hcard : CartanMatrix.A m p p = 2 := by simp [CartanMatrix.A]
    have hcoef : ggQ2xCT_Acoef p p = 2 := by simp [ggQ2xCT_Acoef]
    rw [hcard, hcoef]
    norm_num
  · by_cases hU : (p : ℕ) + 1 = (q : ℕ)
    · have hdisj : (p : ℕ) + 1 = (q : ℕ) ∨ (q : ℕ) + 1 = (p : ℕ) := Or.inl hU
      have hcard : CartanMatrix.A m p q = -1 := by
        simp only [CartanMatrix.A, Matrix.of_apply, if_neg hpq, if_pos hdisj]
      have hcoef : ggQ2xCT_Acoef p q = 2 := by
        simp only [ggQ2xCT_Acoef, if_neg hpq, if_pos hdisj]
      rw [hcard, hcoef]
      decide
    · by_cases hV : (q : ℕ) + 1 = (p : ℕ)
      · have hdisj : (p : ℕ) + 1 = (q : ℕ) ∨ (q : ℕ) + 1 = (p : ℕ) := Or.inr hV
        have hcard : CartanMatrix.A m p q = -1 := by
          simp only [CartanMatrix.A, Matrix.of_apply, if_neg hpq, if_pos hdisj]
        have hcoef : ggQ2xCT_Acoef p q = 2 := by
          simp only [ggQ2xCT_Acoef, if_neg hpq, if_pos hdisj]
        rw [hcard, hcoef]
        decide
      · have hdisj : ¬ ((p : ℕ) + 1 = (q : ℕ) ∨ (q : ℕ) + 1 = (p : ℕ)) :=
          fun hh => hh.elim hU hV
        have hcard : CartanMatrix.A m p q = 0 := by
          simp only [CartanMatrix.A, Matrix.of_apply, if_neg hpq, if_neg hdisj]
        have hcoef : ggQ2xCT_Acoef p q = 0 := by
          simp only [ggQ2xCT_Acoef, if_neg hpq, if_neg hdisj]
        rw [hcard, hcoef]
        norm_num

private theorem ggQ2xCT_sumA_plus {m : ℕ} (p : Fin m) (d : Fin m → ZMod 3) :
    (∑ q : Fin m, ggQ2xCT_Acoef p q * d q)
        + (if h : (p : ℕ) + 1 < m then d (ggQ2xCT_succ p h) else 0)
        + (if h : 0 < (p : ℕ) then d (ggQ2xCT_pred p) else 0)
      = 2 * d p := by
  have hpt : ∀ q : Fin m, ggQ2xCT_Acoef p q * d q
      + (if (p : ℕ) + 1 = (q : ℕ) then d q else 0)
      + (if (q : ℕ) + 1 = (p : ℕ) then d q else 0)
      = 2 * (if p = q then d q else 0) := by
    intro q
    by_cases hpq : p = q
    · subst hpq
      have h1 : ¬ ((p : ℕ) + 1 = (p : ℕ)) := by omega
      simp [ggQ2xCT_Acoef, h1]
    · by_cases hU : (p : ℕ) + 1 = (q : ℕ)
      · by_cases hV : (q : ℕ) + 1 = (p : ℕ)
        · exact (by omega : False).elim
        · simp [ggQ2xCT_Acoef, hpq, hU, hV]
          rw [show (2 : ZMod 3) * d q + d q = 3 * d q by ring,
            show (3 : ZMod 3) = 0 by decide, zero_mul]
      · by_cases hV : (q : ℕ) + 1 = (p : ℕ)
        · simp [ggQ2xCT_Acoef, hpq, hU, hV]
          rw [show (2 : ZMod 3) * d q + d q = 3 * d q by ring,
            show (3 : ZMod 3) = 0 by decide, zero_mul]
        · simp [ggQ2xCT_Acoef, hpq, hU, hV]
  have h1 : (∑ q : Fin m, (ggQ2xCT_Acoef p q * d q
      + (if (p : ℕ) + 1 = (q : ℕ) then d q else 0)
      + (if (q : ℕ) + 1 = (p : ℕ) then d q else 0)))
      = (∑ q : Fin m, ggQ2xCT_Acoef p q * d q)
        + (∑ q : Fin m, (if (p : ℕ) + 1 = (q : ℕ) then d q else 0))
        + (∑ q : Fin m, (if (q : ℕ) + 1 = (p : ℕ) then d q else 0)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h2 : (∑ q : Fin m, (ggQ2xCT_Acoef p q * d q
      + (if (p : ℕ) + 1 = (q : ℕ) then d q else 0)
      + (if (q : ℕ) + 1 = (p : ℕ) then d q else 0)))
      = ∑ q : Fin m, 2 * (if p = q then d q else 0) :=
    Finset.sum_congr rfl (fun q _ => hpt q)
  rw [h2] at h1
  rw [← Finset.mul_sum, Finset.sum_ite_eq] at h1
  simp only [Finset.mem_univ, if_true] at h1
  rw [ggQ2xCT_sum_succ, ggQ2xCT_sum_pred] at h1
  exact h1.symm

private theorem ggQ2xCT_cartan_A (D : GGQ2Lin 3) {m : ℕ} (e : Fin m ≃ D.ι)
    (he : D.coxeter = (CoxeterMatrix.A m).reindex e) (i j : Fin m) :
    D.cartan (e i) (e j) = CartanMatrix.A m i j := by
  by_cases hij : i = j
  · subst hij
    rw [D.isCartan.1 (e i)]
    simp [CartanMatrix.A]
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    have hcox : D.coxeter (e i) (e j) = (CoxeterMatrix.A m) i j := by
      rw [he, CoxeterMatrix.reindex_apply]
      simp
    have hlabel : (CoxeterMatrix.A m) i j = 2 ∨ (CoxeterMatrix.A m) i j = 3 := by
      simp only [CoxeterMatrix.A, Matrix.of_apply]
      rw [if_neg hij]
      by_cases h : (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ)
      · exact Or.inr (if_pos h)
      · exact Or.inl (if_neg h)
    rcases hlabel with h2 | h3
    · have hA0 : CartanMatrix.A m i j = 0 := by
        simp only [CartanMatrix.A, Matrix.of_apply, if_neg hij]
        split_ifs with hh
        · exfalso
          have hcontra : (CoxeterMatrix.A m) i j = 3 := by
            simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hij]
            exact if_pos (Or.symm hh)
          omega
        · rfl
      rcases D.isCartan.2 (e i) (e j) hne with ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ |
        ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · rw [h1, hA0]
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega
    · have hadj : (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) := by
        by_contra hh
        have hcontra : (CoxeterMatrix.A m) i j = 2 := by
          simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hij]
          exact if_neg (fun hD => hh (Or.symm hD))
        omega
      have hAneg : CartanMatrix.A m i j = -1 := by
        simp only [CartanMatrix.A, Matrix.of_apply, if_neg hij]
        exact if_pos hadj
      rcases D.isCartan.2 (e i) (e j) hne with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ |
        ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · rw [hcox] at hm; omega
      · rw [h1, hAneg]
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega

private theorem ggQ2xCT_rowA (D : GGQ2Lin 3) {m : ℕ} (e : Fin m ≃ D.ι)
    (he : D.coxeter = (CoxeterMatrix.A m).reindex e) (c : D.ι → ZMod 3)
    (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) (p : Fin m) :
    (if h : (p : ℕ) + 1 < m then c (e (ggQ2xCT_succ p h)) else 0)
      + (if h : 0 < (p : ℕ) then c (e (ggQ2xCT_pred p)) else 0)
      = 2 * c (e p) := by
  have h := hc (e p)
  rw [← Equiv.sum_comp e (fun j => (D.cartan (e p) j : ZMod 3) * c j)] at h
  have h2 : (∑ q : Fin m, (D.cartan (e p) (e q) : ZMod 3) * c (e q))
      = ∑ q : Fin m, ggQ2xCT_Acoef p q * c (e q) := by
    apply Finset.sum_congr rfl
    intro q _
    rw [ggQ2xCT_cartan_A D e he p q, ggQ2xCT_coefA p q]
  have hsum : (∑ q : Fin m, ggQ2xCT_Acoef p q * c (e q)) = 0 := by
    rw [← h2]
    exact h
  have hs := ggQ2xCT_sumA_plus p (fun q => c (e q))
  rw [hsum] at hs
  simpa using hs

private theorem ggQ2xCT_rowA_mid (D : GGQ2Lin 3) {m : ℕ} (e : Fin m ≃ D.ι)
    (he : D.coxeter = (CoxeterMatrix.A m).reindex e) (c : D.ι → ZMod 3)
    (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) (p : Fin m)
    (hp : 1 ≤ (p : ℕ)) (hp' : (p : ℕ) + 1 < m) :
    c (e ⟨(p : ℕ) + 1, hp'⟩) + c (e ⟨(p : ℕ) - 1, by omega⟩) = 2 * c (e p) := by
  have hr := ggQ2xCT_rowA D e he c hc p
  rw [dif_pos hp', dif_pos (by omega : 0 < (p : ℕ))] at hr
  have hpred : ggQ2xCT_pred p = (⟨(p : ℕ) - 1, by omega⟩ : Fin m) := Fin.ext rfl
  have hsucc : ggQ2xCT_succ p hp' = (⟨(p : ℕ) + 1, hp'⟩ : Fin m) := Fin.ext rfl
  rw [hpred, hsucc] at hr
  exact hr

private theorem ggQ2xCT_rowA_zero (D : GGQ2Lin 3) {m : ℕ} (e : Fin m ≃ D.ι)
    (he : D.coxeter = (CoxeterMatrix.A m).reindex e) (c : D.ι → ZMod 3)
    (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) (hm0 : 0 < m) (hm2 : 2 ≤ m) :
    2 * c (e ⟨0, hm0⟩) = c (e ⟨1, by omega⟩) := by
  have hr := ggQ2xCT_rowA D e he c hc (⟨0, hm0⟩ : Fin m)
  have h1 : (0 : ℕ) + 1 < m := by omega
  rw [dif_pos h1, dif_neg (Nat.lt_irrefl 0), add_zero] at hr
  have hsucc : ggQ2xCT_succ (⟨0, hm0⟩ : Fin m) h1 = (⟨1, by omega⟩ : Fin m) := Fin.ext rfl
  rw [hsucc] at hr
  exact hr.symm

private theorem ggQ2xCT_cartan_of_labels (D : GGQ2Lin 3) {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (e : Γ ≃ D.ι) {M : CoxeterMatrix Γ} (hM : D.coxeter = M.reindex e)
    (hM23 : ∀ i j, i ≠ j → M i j = 2 ∨ M i j = 3) (C : Matrix Γ Γ ℤ)
    (hC0 : ∀ i j, i ≠ j → M i j = 2 → C i j = 0)
    (hC3 : ∀ i j, i ≠ j → M i j = 3 → C i j = -1) (hCii : ∀ i, C i i = 2) (i j : Γ) :
    D.cartan (e i) (e j) = C i j := by
  by_cases hij : i = j
  · subst hij
    rw [D.isCartan.1, hCii]
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    have hcox : D.coxeter (e i) (e j) = M i j := by
      rw [hM, CoxeterMatrix.reindex_apply]
      simp
    rcases hM23 i j hij with h2 | h3
    · rw [hC0 i j hij h2]
      rcases D.isCartan.2 (e i) (e j) hne with ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ |
        ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · exact h1
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega
    · rw [hC3 i j hij h3]
      rcases D.isCartan.2 (e i) (e j) hne with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ |
        ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · rw [hcox] at hm; omega
      · exact h1
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega

private theorem ggQ2xCT_cartan_E6 (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (i j : Fin 6) :
    D.cartan (e i) (e j) = CartanMatrix.E 6 i j :=
  ggQ2xCT_cartan_of_labels D e hE
    (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₆])
    (CartanMatrix.E 6)
    (by
      intro i j hij h
      fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₆, CartanMatrix.E])
    (by
      intro i j hij h
      fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₆, CartanMatrix.E])
    (by intro i; fin_cases i <;> decide) i j

private theorem ggQ2xCT_cartan_D (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD n).reindex e) (i j : Fin n) :
    D.cartan (e i) (e j) = CartanMatrix.D n i j :=
  ggQ2xCT_cartan_of_labels D e hD
    (by
      intro i j hij
      by_cases h : CartanMatrix.D n i j = 0
      · exact Or.inl (by rw [ggCoxeterMatrixD_apply]; simp [hij, h])
      · exact Or.inr (by rw [ggCoxeterMatrixD_apply]; simp [hij, h]))
    (CartanMatrix.D n)
    (by
      intro i j hij h
      by_cases h0 : CartanMatrix.D n i j = 0
      · exact h0
      · rw [ggCoxeterMatrixD_apply, if_neg hij] at h
        simp [h0] at h)
    (by
      intro i j hij h
      have hne : CartanMatrix.D n i j ≠ 0 := by
        intro h0; rw [ggCoxeterMatrixD_apply, if_neg hij, h0] at h; simp at h
      rcases (CartanMatrix.isSimplyLaced_D n) hij with h0 | hm1
      · exact absurd h0 hne
      · exact hm1)
    (by intro i; simp [CartanMatrix.D]) i j

private theorem ggQ2xCT_D_eq_A (n : ℕ) (p q : Fin n) (hp : (p:ℕ) + 4 ≤ n) :
    CartanMatrix.D n p q = CartanMatrix.A n p q := by
  have hn2 : 2 ≤ n := by omega
  simp only [CartanMatrix.D, CartanMatrix.A, Matrix.of_apply]
  split_ifs <;> omega

private theorem ggQ2xCT_rowD (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD n).reindex e) (c : D.ι → ZMod 3)
    (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) (p : Fin n)
    (hp : (p:ℕ) + 4 ≤ n) :
    (if h : (p:ℕ) + 1 < n then c (e (ggQ2xCT_succ p h)) else 0)
      + (if h : 0 < (p:ℕ) then c (e (ggQ2xCT_pred p)) else 0)
      = 2 * c (e p) := by
  have h := hc (e p)
  rw [← Equiv.sum_comp e (fun j => (D.cartan (e p) j : ZMod 3) * c j)] at h
  have h2 : (∑ q : Fin n, (D.cartan (e p) (e q) : ZMod 3) * c (e q))
      = ∑ q : Fin n, ggQ2xCT_Acoef p q * c (e q) := by
    apply Finset.sum_congr rfl
    intro q _
    rw [ggQ2xCT_cartan_D D e hD p q, ggQ2xCT_D_eq_A n p q hp, ggQ2xCT_coefA p q]
  have hsum : (∑ q : Fin n, ggQ2xCT_Acoef p q * c (e q)) = 0 := by
    rw [← h2]
    exact h
  have hs := ggQ2xCT_sumA_plus p (fun q => c (e q))
  rw [hsum] at hs
  simpa using hs

private theorem ggQ2xCT_two_leaf : ∀ x y : ZMod 3, 2 * x + 2 * y = 0 → 2 * x = y := by
  decide +kernel

private theorem ggQ2xCT_Dcoef_n2 (n : ℕ) (hn : 4 ≤ n) (q : Fin n) :
    ((CartanMatrix.D n (⟨n-2, by omega⟩ : Fin n) q : ℤ) : ZMod 3)
      = if q = (⟨n-2, by omega⟩ : Fin n) then 2
        else if q = (⟨n-3, by omega⟩ : Fin n) then 2 else 0 := by
  by_cases h1 : q = (⟨n-2, by omega⟩ : Fin n)
  · rw [h1]
    simp [CartanMatrix.D]
  · by_cases h2 : q = (⟨n-3, by omega⟩ : Fin n)
    · rw [if_neg h1, if_pos h2, h2]
      rw [show CartanMatrix.D n (⟨n-2, by omega⟩ : Fin n) (⟨n-3, by omega⟩ : Fin n) = -1 from by
        simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
        split_ifs <;> omega]
      decide
    · rw [if_neg h1, if_neg h2]
      rw [show CartanMatrix.D n (⟨n-2, by omega⟩ : Fin n) q = 0 from by
        have ha : (((⟨n-2, by omega⟩ : Fin n)) : ℕ) = n - 2 := rfl
        have hb : (((⟨n-3, by omega⟩ : Fin n)) : ℕ) = n - 3 := rfl
        have h1' : (q : ℕ) ≠ n - 2 := fun hh => h1 (Fin.ext (by rw [hh, ha]))
        have h2' : (q : ℕ) ≠ n - 3 := fun hh => h2 (Fin.ext (by rw [hh, hb]))
        simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, ha, hb]
        split_ifs <;> omega]
      norm_num

private theorem ggQ2xCT_Dcoef_n1 (n : ℕ) (hn : 4 ≤ n) (q : Fin n) :
    ((CartanMatrix.D n (⟨n-1, by omega⟩ : Fin n) q : ℤ) : ZMod 3)
      = if q = (⟨n-1, by omega⟩ : Fin n) then 2
        else if q = (⟨n-3, by omega⟩ : Fin n) then 2 else 0 := by
  by_cases h1 : q = (⟨n-1, by omega⟩ : Fin n)
  · rw [h1]
    simp [CartanMatrix.D]
  · by_cases h2 : q = (⟨n-3, by omega⟩ : Fin n)
    · rw [if_neg h1, if_pos h2, h2]
      rw [show CartanMatrix.D n (⟨n-1, by omega⟩ : Fin n) (⟨n-3, by omega⟩ : Fin n) = -1 from by
        simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
        split_ifs <;> omega]
      decide
    · rw [if_neg h1, if_neg h2]
      rw [show CartanMatrix.D n (⟨n-1, by omega⟩ : Fin n) q = 0 from by
        have ha : (((⟨n-1, by omega⟩ : Fin n)) : ℕ) = n - 1 := rfl
        have hb : (((⟨n-3, by omega⟩ : Fin n)) : ℕ) = n - 3 := rfl
        have h1' : (q : ℕ) ≠ n - 1 := fun hh => h1 (Fin.ext (by rw [hh, ha]))
        have h2' : (q : ℕ) ≠ n - 3 := fun hh => h2 (Fin.ext (by rw [hh, hb]))
        simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, ha, hb]
        split_ifs <;> omega]
      norm_num

private theorem ggQ2xCT_Dcoef_n3 (n : ℕ) (hn : 4 ≤ n) (q : Fin n) :
    ((CartanMatrix.D n (⟨n-3, by omega⟩ : Fin n) q : ℤ) : ZMod 3)
      = if q = (⟨n-3, by omega⟩ : Fin n) then 2
        else if q = (⟨n-4, by omega⟩ : Fin n) then 2
        else if q = (⟨n-2, by omega⟩ : Fin n) then 2
        else if q = (⟨n-1, by omega⟩ : Fin n) then 2 else 0 := by
  by_cases h1 : q = (⟨n-3, by omega⟩ : Fin n)
  · rw [h1]
    simp [CartanMatrix.D]
  · by_cases h2 : q = (⟨n-4, by omega⟩ : Fin n)
    · rw [if_neg h1, if_pos h2, h2]
      rw [show CartanMatrix.D n (⟨n-3, by omega⟩ : Fin n) (⟨n-4, by omega⟩ : Fin n) = -1 from by
        simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
        split_ifs <;> omega]
      decide
    · by_cases h3 : q = (⟨n-2, by omega⟩ : Fin n)
      · rw [if_neg h1, if_neg h2, if_pos h3, h3]
        rw [show CartanMatrix.D n (⟨n-3, by omega⟩ : Fin n) (⟨n-2, by omega⟩ : Fin n) = -1 from by
          simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
          split_ifs <;> omega]
        decide
      · by_cases h4 : q = (⟨n-1, by omega⟩ : Fin n)
        · rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4, h4]
          rw [show CartanMatrix.D n (⟨n-3, by omega⟩ : Fin n) (⟨n-1, by omega⟩ : Fin n) = -1 from by
            simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
            split_ifs <;> omega]
          decide
        · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
          rw [show CartanMatrix.D n (⟨n-3, by omega⟩ : Fin n) q = 0 from by
            have ha : (((⟨n-3, by omega⟩ : Fin n)) : ℕ) = n - 3 := rfl
            have hb : (((⟨n-4, by omega⟩ : Fin n)) : ℕ) = n - 4 := rfl
            have hc : (((⟨n-2, by omega⟩ : Fin n)) : ℕ) = n - 2 := rfl
            have hd : (((⟨n-1, by omega⟩ : Fin n)) : ℕ) = n - 1 := rfl
            have h1' : (q : ℕ) ≠ n - 3 := fun hh => h1 (Fin.ext (by rw [hh, ha]))
            have h2' : (q : ℕ) ≠ n - 4 := fun hh => h2 (Fin.ext (by rw [hh, hb]))
            have h3' : (q : ℕ) ≠ n - 2 := fun hh => h3 (Fin.ext (by rw [hh, hc]))
            have h4' : (q : ℕ) ≠ n - 1 := fun hh => h4 (Fin.ext (by rw [hh, hd]))
            simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, ha, hb, hc, hd]
            split_ifs <;> omega]
          norm_num

private theorem ggQ2xCT_sum_leaf {n : ℕ} (hn : 4 ≤ n) (a b : Fin n) (hab : a ≠ b)
    (hcoef : ∀ q, ((CartanMatrix.D n a q : ℤ) : ZMod 3) =
      if q = a then 2 else if q = b then 2 else 0)
    (f : Fin n → ZMod 3) :
    (∑ q : Fin n, ((CartanMatrix.D n a q : ℤ) : ZMod 3) * f q) = 2 * f a + 2 * f b := by
  have hpt : ∀ q : Fin n, ((((CartanMatrix.D n a q : ℤ) : ZMod 3) * f q))
      = (if q = a then 2 * f q else 0) + (if q = b then 2 * f q else 0) := by
    intro q
    rw [hcoef q]
    by_cases h1 : q = a
    · subst h1
      simp [hab]
    · by_cases h2 : q = b
      · subst h2
        simp [h1]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun q _ => hpt q), Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

private theorem ggQ2xCT_rowD_n2 (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD n).reindex e) (c : D.ι → ZMod 3)
    (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) (hn : 4 ≤ n) :
    2 * c (e ⟨n-2, by omega⟩) = c (e ⟨n-3, by omega⟩) := by
  have h := hc (e ⟨n-2, by omega⟩)
  rw [← Equiv.sum_comp e (fun j => (D.cartan (e ⟨n-2, by omega⟩) j : ZMod 3) * c j)] at h
  have h2 : (∑ q : Fin n, (D.cartan (e ⟨n-2, by omega⟩) (e q) : ZMod 3) * c (e q))
      = ∑ q : Fin n, ((CartanMatrix.D n (⟨n-2, by omega⟩ : Fin n) q : ℤ) : ZMod 3) * c (e q) := by
    apply Finset.sum_congr rfl
    intro q _
    rw [ggQ2xCT_cartan_D D e hD]
  rw [h2] at h
  rw [ggQ2xCT_sum_leaf hn (⟨n-2, by omega⟩ : Fin n) (⟨n-3, by omega⟩ : Fin n) (by
      intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_mk] at hv; omega)
    (ggQ2xCT_Dcoef_n2 n hn) (fun q => c (e q))] at h
  exact ggQ2xCT_two_leaf _ _ h

private theorem ggQ2xCT_four_fork : ∀ x w y z : ZMod 3,
    2 * x + 2 * w + 2 * y + 2 * z = 0 → 2 * x = w + y + z := by decide +kernel

private theorem ggQ2xCT_two_eq : ∀ x y : ZMod 3, 2 * x = y → x = 2 * y := by
  decide +kernel

private theorem ggQ2xCT_two_zero : ∀ x : ZMod 3, 2 * x = 0 → x = 0 := by
  decide +kernel

private theorem ggQ2xCT_tzero : ∀ A t : ZMod 3,
    2 * (A * t) = (A - 1) * t + 2 * (A * t) + 2 * (A * t) → t = 0 := by decide +kernel

private theorem ggQ2xCT_sum_fork {n : ℕ} (hn : 4 ≤ n) (a b c d : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hcoef : ∀ q, ((CartanMatrix.D n a q : ℤ) : ZMod 3)
      = if q = a then 2 else if q = b then 2 else if q = c then 2 else if q = d then 2 else 0)
    (f : Fin n → ZMod 3) :
    (∑ q : Fin n, ((CartanMatrix.D n a q : ℤ) : ZMod 3) * f q)
      = 2 * f a + 2 * f b + 2 * f c + 2 * f d := by
  have hpt : ∀ q : Fin n, ((((CartanMatrix.D n a q : ℤ) : ZMod 3) * f q))
      = (if q = a then 2 * f q else 0) + (if q = b then 2 * f q else 0)
        + (if q = c then 2 * f q else 0) + (if q = d then 2 * f q else 0) := by
    intro q
    rw [hcoef q]
    by_cases h1 : q = a
    · subst h1
      simp [hab, hac, had]
    · by_cases h2 : q = b
      · subst h2
        simp [h1, hbc, hbd]
      · by_cases h3 : q = c
        · subst h3
          simp [h1, h2, hcd]
        · by_cases h4 : q = d
          · subst h4
            simp [h1, h2, h3]
          · simp [h1, h2, h3, h4]
  rw [Finset.sum_congr rfl (fun q _ => hpt q)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

private theorem ggQ2xCT_rowD_n1 (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD n).reindex e) (c : D.ι → ZMod 3)
    (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) (hn : 4 ≤ n) :
    2 * c (e ⟨n-1, by omega⟩) = c (e ⟨n-3, by omega⟩) := by
  have h := hc (e ⟨n-1, by omega⟩)
  rw [← Equiv.sum_comp e (fun j => (D.cartan (e ⟨n-1, by omega⟩) j : ZMod 3) * c j)] at h
  have h2 : (∑ q : Fin n, (D.cartan (e ⟨n-1, by omega⟩) (e q) : ZMod 3) * c (e q))
      = ∑ q : Fin n, ((CartanMatrix.D n (⟨n-1, by omega⟩ : Fin n) q : ℤ) : ZMod 3) * c (e q) := by
    apply Finset.sum_congr rfl
    intro q _
    rw [ggQ2xCT_cartan_D D e hD]
  rw [h2] at h
  rw [ggQ2xCT_sum_leaf hn (⟨n-1, by omega⟩ : Fin n) (⟨n-3, by omega⟩ : Fin n) (by
      intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_mk] at hv; omega)
    (ggQ2xCT_Dcoef_n1 n hn) (fun q => c (e q))] at h
  exact ggQ2xCT_two_leaf _ _ h

private theorem ggQ2xCT_rowD_n3 (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD n).reindex e) (c : D.ι → ZMod 3)
    (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) (hn : 4 ≤ n) :
    2 * c (e ⟨n-3, by omega⟩) = c (e ⟨n-4, by omega⟩) + c (e ⟨n-2, by omega⟩)
      + c (e ⟨n-1, by omega⟩) := by
  have h := hc (e ⟨n-3, by omega⟩)
  rw [← Equiv.sum_comp e (fun j => (D.cartan (e ⟨n-3, by omega⟩) j : ZMod 3) * c j)] at h
  have h2 : (∑ q : Fin n, (D.cartan (e ⟨n-3, by omega⟩) (e q) : ZMod 3) * c (e q))
      = ∑ q : Fin n, ((CartanMatrix.D n (⟨n-3, by omega⟩ : Fin n) q : ℤ) : ZMod 3) * c (e q) := by
    apply Finset.sum_congr rfl
    intro q _
    rw [ggQ2xCT_cartan_D D e hD]
  rw [h2] at h
  rw [ggQ2xCT_sum_fork hn (⟨n-3, by omega⟩ : Fin n) (⟨n-4, by omega⟩ : Fin n)
      (⟨n-2, by omega⟩ : Fin n) (⟨n-1, by omega⟩ : Fin n)
      (by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_mk] at hv; omega)
      (by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_mk] at hv; omega)
      (by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_mk] at hv; omega)
      (by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_mk] at hv; omega)
      (by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_mk] at hv; omega)
      (by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_mk] at hv; omega)
      (ggQ2xCT_Dcoef_n3 n hn) (fun q => c (e q))] at h
  exact ggQ2xCT_four_fork _ _ _ _ h

private theorem ggQ2xCT_kernel_D (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD n).reindex e) (hn : 4 ≤ n)
    (c : D.ι → ZMod 3) (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) : c = 0 := by
  let d : ℕ → ZMod 3 := fun k => if h : k < n then c (e ⟨k, h⟩) else 0
  have hd : ∀ k (h : k < n), d k = c (e ⟨k, h⟩) := fun k h => by
    show (if h' : k < n then c (e ⟨k, h'⟩) else 0) = c (e ⟨k, h⟩)
    rw [dif_pos h]
  have hn0 : 0 < n := by omega
  have h0 : 2 * d 0 = d 1 := by
    have hr := ggQ2xCT_rowD D e hD c hc (⟨0, hn0⟩ : Fin n) (by omega)
    rw [dif_pos (by omega : (0:ℕ) + 1 < n), dif_neg (Nat.lt_irrefl 0), add_zero] at hr
    rw [hd 0 hn0, hd 1 (by omega : 1 < n)]
    exact hr.symm
  have hstep : ∀ k, 1 ≤ k → k + 1 < n - 2 → d (k + 1) + d (k - 1) = 2 * d k := by
    intro k hk1 hk2
    have hk : k < n := by omega
    have hp : ((⟨k, hk⟩ : Fin n) : ℕ) + 4 ≤ n := by
      simp only [Fin.val_mk]; omega
    have hr := ggQ2xCT_rowD D e hD c hc (⟨k, hk⟩ : Fin n) hp
    rw [dif_pos (by omega : k + 1 < n), dif_pos (by omega : 0 < k)] at hr
    rw [hd (k + 1) (by omega), hd k hk, hd (k - 1) (by omega)]
    convert hr using 2 <;> exact Fin.ext rfl
  have hrec := ggQ2xCT_rec (n - 2) d h0 hstep
  have hx := ggQ2xCT_rowD_n2 D e hD c hc hn
  have hy := ggQ2xCT_rowD_n1 D e hD c hc hn
  have hz := ggQ2xCT_rowD_n3 D e hD c hc hn
  have h3v : c (e ⟨n-3, by omega⟩) = ((n-2:ℕ):ZMod 3) * d 0 := by
    rw [← hd (n-3) (by omega : n - 3 < n)]
    simpa only [show n - 3 + 1 = n - 2 by omega] using hrec (n - 3) (by omega)
  have h4v : c (e ⟨n-4, by omega⟩) = ((n-3:ℕ):ZMod 3) * d 0 := by
    rw [← hd (n-4) (by omega : n - 4 < n)]
    simpa only [show n - 4 + 1 = n - 3 by omega] using hrec (n - 4) (by omega)
  have hxv : c (e ⟨n-2, by omega⟩) = 2 * (((n-2:ℕ):ZMod 3) * d 0) := by
    have h2 := hx
    rw [h3v] at h2
    exact ggQ2xCT_two_eq _ _ h2
  have hyv : c (e ⟨n-1, by omega⟩) = 2 * (((n-2:ℕ):ZMod 3) * d 0) := by
    have h2 := hy
    rw [h3v] at h2
    exact ggQ2xCT_two_eq _ _ h2
  have hzv : 2 * (((n-2:ℕ):ZMod 3) * d 0)
      = ((n-3:ℕ):ZMod 3) * d 0 + 2 * (((n-2:ℕ):ZMod 3) * d 0)
        + 2 * (((n-2:ℕ):ZMod 3) * d 0) := by
    have h := hz
    rw [h3v, h4v, hxv, hyv] at h
    exact h
  have ht : d 0 = 0 := by
    have hBA : ((n-3:ℕ):ZMod 3) = ((n-2:ℕ):ZMod 3) - 1 := by
      rw [show n - 3 = n - 2 - 1 by omega, Nat.cast_sub (by omega : 1 ≤ n - 2), Nat.cast_one]
    rw [hBA] at hzv
    exact ggQ2xCT_tzero _ _ hzv
  have hdz : ∀ k, k < n - 2 → d k = 0 := by
    intro k hk
    rw [hrec k hk, ht, mul_zero]
  have htail2 : c (e ⟨n-2, by omega⟩) = 0 := by simp [hxv, ht]
  have htail1 : c (e ⟨n-1, by omega⟩) = 0 := by simp [hyv, ht]
  funext i
  obtain ⟨k, rfl⟩ := e.surjective i
  by_cases hk : (k:ℕ) < n - 2
  · have hzero := hdz k hk
    rw [hd k k.isLt] at hzero
    exact hzero
  · have hk2 : (k:ℕ) = n - 2 ∨ (k:ℕ) = n - 1 := by omega
    rcases hk2 with hk2 | hk2
    · have hki : k = (⟨n-2, by omega⟩ : Fin n) := Fin.ext hk2
      rw [hki]; exact htail2
    · have hki : k = (⟨n-1, by omega⟩ : Fin n) := Fin.ext hk2
      rw [hki]; exact htail1
private theorem ggQ2xCT_label2 (D : GGQ2Lin 3) {i j : D.ι} (hij : i ≠ j)
    (h : D.coxeter i j = 2) : D.cartan i j = 0 := by
  rcases D.isCartan.2 i j hij with ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
  · exact h1
  · rw [h] at hm; omega
  · rw [h] at hm; omega
  · rw [h] at hm; omega

private theorem ggQ2xCT_label3 (D : GGQ2Lin 3) {i j : D.ι} (hij : i ≠ j)
    (h : D.coxeter i j = 3) : D.cartan i j = -1 := by
  rcases D.isCartan.2 i j hij with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
  · rw [h] at hm; omega
  · exact h1
  · rw [h] at hm; omega
  · rw [h] at hm; omega

private theorem ggQ2xCT_label4 (D : GGQ2Lin 3) {i j : D.ι} (hij : i ≠ j)
    (h : D.coxeter i j = 4) :
    (D.cartan i j = -1 ∧ D.cartan j i = -2) ∨ (D.cartan i j = -2 ∧ D.cartan j i = -1) := by
  rcases D.isCartan.2 i j hij with ⟨hm, -, -⟩ | ⟨hm, -, -⟩ | ⟨hm, h1, h2, h3⟩ | ⟨hm, -, -, -⟩
  · rw [h] at hm; omega
  · rw [h] at hm; omega
  · set C := D.cartan i j with hCdef
    have hle : -2 ≤ C := by nlinarith [h1, h2, h3]
    interval_cases C <;> omega
  · rw [h] at hm; omega

private def ggQ2xCT_F4a : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0; -1, 2, -2, 0; 0, -1, 2, -1; 0, 0, -1, 2]

private def ggQ2xCT_F4b : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0; -1, 2, -1, 0; 0, -2, 2, -1; 0, 0, -1, 2]

private theorem ggQ2xCT_kernel_F4a_dec : ∀ d : Fin 4 → ZMod 3,
    (∀ p, ∑ q, ((ggQ2xCT_F4a p q : ℤ) : ZMod 3) * d q = 0) → d = 0 := by decide +kernel

private theorem ggQ2xCT_kernel_F4b_dec : ∀ d : Fin 4 → ZMod 3,
    (∀ p, ∑ q, ((ggQ2xCT_F4b p q : ℤ) : ZMod 3) * d q = 0) → d = 0 := by decide +kernel

private theorem ggQ2xCT_kernel_of_reindex {m : ℕ} (D : GGQ2Lin 3) (e : Fin m ≃ D.ι)
    (C : Matrix (Fin m) (Fin m) ℤ)
    (hC : ∀ a b, D.cartan (e a) (e b) = C a b) (c : D.ι → ZMod 3)
    (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0)
    (hdec : ∀ d : Fin m → ZMod 3, (∀ p, ∑ q, ((C p q : ℤ) : ZMod 3) * d q = 0) → d = 0) :
    c = 0 := by
  let d : Fin m → ZMod 3 := fun p => c (e p)
  have hrow : ∀ p : Fin m, ∑ q : Fin m, ((C p q : ℤ) : ZMod 3) * d q = 0 := by
    intro p
    have h := hc (e p)
    rw [← Equiv.sum_comp e (fun j => (D.cartan (e p) j : ZMod 3) * c j)] at h
    have h2 : (∑ q : Fin m, (D.cartan (e p) (e q) : ZMod 3) * c (e q))
        = ∑ q : Fin m, ((C p q : ℤ) : ZMod 3) * d q := by
      apply Finset.sum_congr rfl
      intro q _
      rw [hC p q]
    rw [h2] at h
    exact h
  have hd0 := hdec d hrow
  funext i
  have hdi : d (e.symm i) = c i := by
    show c (e (e.symm i)) = c i
    rw [Equiv.apply_symm_apply]
  have h1 : d (e.symm i) = 0 := congrFun hd0 (e.symm i)
  rw [hdi] at h1
  exact h1

private theorem ggQ2xCT_cartan_F4 (D : GGQ2Lin 3) (e : Fin 4 ≃ D.ι)
    (hF : D.coxeter = CoxeterMatrix.F₄.reindex e) :
    (∀ a b, D.cartan (e a) (e b) = ggQ2xCT_F4a a b) ∨
      (∀ a b, D.cartan (e a) (e b) = ggQ2xCT_F4b a b) := by
  have hFlabel : ∀ a b : Fin 4, D.coxeter (e a) (e b) = CoxeterMatrix.F₄ a b := by
    intro a b; rw [hF, CoxeterMatrix.reindex_apply]; simp
  have h12 : D.coxeter (e 1) (e 2) = 4 := by rw [hFlabel]; decide
  have hlab3 : ∀ a b : Fin 4, a ≠ b → CoxeterMatrix.F₄ a b = 3 → D.cartan (e a) (e b) = -1 :=
    fun a b hab h => ggQ2xCT_label3 D (e.injective.ne hab) (by rw [hFlabel]; exact h)
  have hlab2 : ∀ a b : Fin 4, a ≠ b → CoxeterMatrix.F₄ a b = 2 → D.cartan (e a) (e b) = 0 :=
    fun a b hab h => ggQ2xCT_label2 D (e.injective.ne hab) (by rw [hFlabel]; exact h)
  rcases ggQ2xCT_label4 D (e.injective.ne (by decide : (1 : Fin 4) ≠ 2)) h12 with
    ⟨h12a, h12b⟩ | ⟨h12a, h12b⟩
  · right
    have h00 : D.cartan (e 0) (e 0) = 2 := D.isCartan.1 _
    have h11 : D.cartan (e 1) (e 1) = 2 := D.isCartan.1 _
    have h22 : D.cartan (e 2) (e 2) = 2 := D.isCartan.1 _
    have h33 : D.cartan (e 3) (e 3) = 2 := D.isCartan.1 _
    have h01 : D.cartan (e 0) (e 1) = -1 := hlab3 0 1 (by decide) (by decide)
    have h10 : D.cartan (e 1) (e 0) = -1 := hlab3 1 0 (by decide) (by decide)
    have h23 : D.cartan (e 2) (e 3) = -1 := hlab3 2 3 (by decide) (by decide)
    have h32 : D.cartan (e 3) (e 2) = -1 := hlab3 3 2 (by decide) (by decide)
    have h02 : D.cartan (e 0) (e 2) = 0 := hlab2 0 2 (by decide) (by decide)
    have h20 : D.cartan (e 2) (e 0) = 0 := hlab2 2 0 (by decide) (by decide)
    have h03 : D.cartan (e 0) (e 3) = 0 := hlab2 0 3 (by decide) (by decide)
    have h30 : D.cartan (e 3) (e 0) = 0 := hlab2 3 0 (by decide) (by decide)
    have h13 : D.cartan (e 1) (e 3) = 0 := hlab2 1 3 (by decide) (by decide)
    have h31 : D.cartan (e 3) (e 1) = 0 := hlab2 3 1 (by decide) (by decide)
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp_all [ggQ2xCT_F4b, h00, h01, h02, h03, h10, h11, h12a, h12b, h13, h20, h22, h23,
        h30, h31, h32, h33]
  · left
    have h00 : D.cartan (e 0) (e 0) = 2 := D.isCartan.1 _
    have h11 : D.cartan (e 1) (e 1) = 2 := D.isCartan.1 _
    have h22 : D.cartan (e 2) (e 2) = 2 := D.isCartan.1 _
    have h33 : D.cartan (e 3) (e 3) = 2 := D.isCartan.1 _
    have h01 : D.cartan (e 0) (e 1) = -1 := hlab3 0 1 (by decide) (by decide)
    have h10 : D.cartan (e 1) (e 0) = -1 := hlab3 1 0 (by decide) (by decide)
    have h23 : D.cartan (e 2) (e 3) = -1 := hlab3 2 3 (by decide) (by decide)
    have h32 : D.cartan (e 3) (e 2) = -1 := hlab3 3 2 (by decide) (by decide)
    have h02 : D.cartan (e 0) (e 2) = 0 := hlab2 0 2 (by decide) (by decide)
    have h20 : D.cartan (e 2) (e 0) = 0 := hlab2 2 0 (by decide) (by decide)
    have h03 : D.cartan (e 0) (e 3) = 0 := hlab2 0 3 (by decide) (by decide)
    have h30 : D.cartan (e 3) (e 0) = 0 := hlab2 3 0 (by decide) (by decide)
    have h13 : D.cartan (e 1) (e 3) = 0 := hlab2 1 3 (by decide) (by decide)
    have h31 : D.cartan (e 3) (e 1) = 0 := hlab2 3 1 (by decide) (by decide)
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp_all [ggQ2xCT_F4a, h00, h01, h02, h03, h10, h11, h12a, h12b, h13, h20, h22, h23,
        h30, h31, h32, h33]

private theorem ggQ2xCT_kernel_F4 (D : GGQ2Lin 3) (e : Fin 4 ≃ D.ι)
    (hF : D.coxeter = CoxeterMatrix.F₄.reindex e) (c : D.ι → ZMod 3)
    (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) : c = 0 := by
  rcases ggQ2xCT_cartan_F4 D e hF with hC | hC
  · exact ggQ2xCT_kernel_of_reindex D e ggQ2xCT_F4a hC c hc ggQ2xCT_kernel_F4a_dec
  · exact ggQ2xCT_kernel_of_reindex D e ggQ2xCT_F4b hC c hc ggQ2xCT_kernel_F4b_dec

private theorem ggQ2xCT_kernel_E6_dec : ∀ d : Fin 6 → ZMod 3,
    (∀ p, ∑ q, ((CartanMatrix.E 6 p q : ℤ) : ZMod 3) * d q = 0) →
      d 1 = 0 ∧ d 3 = 0 ∧ d 2 = 2 * d 0 ∧ d 4 = d 0 ∧ d 5 = 2 * d 0 := by
  decide +kernel

private theorem ggQ2xCT_cartan_E7 (D : GGQ2Lin 3) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) (i j : Fin 7) :
    D.cartan (e i) (e j) = CartanMatrix.E 7 i j :=
  ggQ2xCT_cartan_of_labels D e hE
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₇])
    (CartanMatrix.E 7)
    (by
      intro i j hij h
      fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₇, CartanMatrix.E])
    (by
      intro i j hij h
      fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₇, CartanMatrix.E])
    (by intro i; fin_cases i <;> decide) i j

private theorem ggQ2xCT_kernel_E7_dec : ∀ d : Fin 7 → ZMod 3,
    (∀ p, ∑ q, ((CartanMatrix.E 7 p q : ℤ) : ZMod 3) * d q = 0) → d = 0 := by
  decide +kernel

private theorem ggQ2xCT_cartan_E8 (D : GGQ2Lin 3) (e : Fin 8 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₈.reindex e) (i j : Fin 8) :
    D.cartan (e i) (e j) = CartanMatrix.E 8 i j :=
  ggQ2xCT_cartan_of_labels D e hE
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₈])
    (CartanMatrix.E 8)
    (by
      intro i j hij h
      fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₈, CartanMatrix.E])
    (by
      intro i j hij h
      fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₈, CartanMatrix.E])
    (by intro i; fin_cases i <;> decide) i j

private theorem ggQ2xCT_dec_E8a : ∀ x0 x1 x2 x3 : ZMod 3,
    (2 * x0 + -x2 = 0) → (2 * x1 + -x3 = 0) → (-x0 + (2 * x2 + -x3) = 0) →
    x1 = 0 ∧ x2 = 2 * x0 ∧ x3 = 0 := by decide +kernel

private theorem ggQ2xCT_dec_E8b : ∀ x0 x4 x5 : ZMod 3,
    (-(2 * x0) + -x4 = 0) → (2 * x4 + -x5 = 0) → x4 = x0 ∧ x5 = 2 * x0 := by
  decide +kernel

private theorem ggQ2xCT_dec_E8c : ∀ x0 x6 x7 : ZMod 3,
    (-x0 + (2 * (2 * x0) + -x6) = 0) → (-(2 * x0) + (2 * x6 + -x7) = 0) →
    (-x6 + 2 * x7 = 0) → x0 = 0 ∧ x6 = 0 ∧ x7 = 0 := by decide +kernel

private theorem ggQ2xCT_kernel_E8_dec (d : Fin 8 → ZMod 3)
    (h : ∀ p, ∑ q, ((CartanMatrix.E 8 p q : ℤ) : ZMod 3) * d q = 0) : d = 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  norm_num [Fin.sum_univ_succ, CartanMatrix.E, Matrix.of_apply] at h0 h1 h2 h3 h4 h5 h6 h7
  obtain ⟨hd1, hd2, hd3⟩ := ggQ2xCT_dec_E8a (d 0) (d 1) (d 2) (d 3) h0 h1 h2
  rw [hd1, hd2, hd3] at h3
  rw [hd3] at h4
  norm_num at h3 h4
  obtain ⟨hd4, hd5⟩ := ggQ2xCT_dec_E8b (d 0) (d 4) (d 5) h3 h4
  rw [hd4] at h5
  rw [hd5] at h5 h6
  norm_num at h5 h6
  obtain ⟨hd0, hd6, hd7⟩ := ggQ2xCT_dec_E8c (d 0) (d 6) (d 7) h5 h6 h7
  funext p
  fin_cases p <;> simp_all

private theorem ggQ2xCT_sum_leaf_gen {m : ℕ} (g : Fin m → ZMod 3) (a b : Fin m) (hab : a ≠ b)
    (β : ZMod 3) (hcoef : ∀ q, g q = if q = a then 2 else if q = b then β else 0)
    (f : Fin m → ZMod 3) :
    (∑ q : Fin m, g q * f q) = 2 * f a + β * f b := by
  have hpt : ∀ q : Fin m, g q * f q
      = (if q = a then 2 * f q else 0) + (if q = b then β * f q else 0) := by
    intro q
    rw [hcoef q]
    by_cases h1 : q = a
    · subst h1; simp [hab]
    · by_cases h2 : q = b
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun q _ => hpt q), Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

private theorem ggQ2xCT_sum_leaf_gen3 {m : ℕ} (g : Fin m → ZMod 3) (a b d : Fin m)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (γ : ZMod 3)
    (hcoef : ∀ q, g q = if q = a then 2 else if q = b then 2 else if q = d then γ else 0)
    (f : Fin m → ZMod 3) :
    (∑ q : Fin m, g q * f q) = 2 * f a + 2 * f b + γ * f d := by
  have hpt : ∀ q : Fin m, g q * f q
      = (if q = a then 2 * f q else 0) + (if q = b then 2 * f q else 0)
        + (if q = d then γ * f q else 0) := by
    intro q
    rw [hcoef q]
    by_cases h1 : q = a
    · subst h1; simp [hab, had]
    · by_cases h2 : q = b
      · subst h2; simp [h1, hbd]
      · by_cases h3 : q = d
        · subst h3; simp [h1, h2]
        · simp [h1, h2, h3]
  rw [Finset.sum_congr rfl (fun q _ => hpt q)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

private theorem ggQ2xCT_B_label_last (n : ℕ) (hn : 3 ≤ n) (q : Fin n)
    (h1 : q ≠ (⟨n-1, by omega⟩ : Fin n)) (h2 : q ≠ (⟨n-2, by omega⟩ : Fin n)) :
    CoxeterMatrix.B n (⟨n-1, by omega⟩ : Fin n) q = 2 := by
  have ha : (((⟨n-1, by omega⟩ : Fin n)) : ℕ) = n - 1 := rfl
  have hb : (((⟨n-2, by omega⟩ : Fin n)) : ℕ) = n - 2 := rfl
  have h1' : (q : ℕ) ≠ n - 1 := fun hh => h1 (Fin.ext (by rw [hh, ha]))
  have h2' : (q : ℕ) ≠ n - 2 := fun hh => h2 (Fin.ext (by rw [hh, hb]))
  simp only [CoxeterMatrix.B, Matrix.of_apply, Fin.ext_iff, ha, hb]
  split_ifs <;> omega

private theorem ggQ2xCT_B_label_n2 (n : ℕ) (hn : 4 ≤ n) (q : Fin n)
    (h1 : q ≠ (⟨n-2, by omega⟩ : Fin n)) (h2 : q ≠ (⟨n-3, by omega⟩ : Fin n))
    (h3 : q ≠ (⟨n-1, by omega⟩ : Fin n)) :
    CoxeterMatrix.B n (⟨n-2, by omega⟩ : Fin n) q = 2 := by
  have ha : (((⟨n-2, by omega⟩ : Fin n)) : ℕ) = n - 2 := rfl
  have hb : (((⟨n-3, by omega⟩ : Fin n)) : ℕ) = n - 3 := rfl
  have hc : (((⟨n-1, by omega⟩ : Fin n)) : ℕ) = n - 1 := rfl
  have h1' : (q : ℕ) ≠ n - 2 := fun hh => h1 (Fin.ext (by rw [hh, ha]))
  have h2' : (q : ℕ) ≠ n - 3 := fun hh => h2 (Fin.ext (by rw [hh, hb]))
  have h3' : (q : ℕ) ≠ n - 1 := fun hh => h3 (Fin.ext (by rw [hh, hc]))
  simp only [CoxeterMatrix.B, Matrix.of_apply, Fin.ext_iff, ha, hb, hc]
  split_ifs <;> omega

private theorem ggQ2xCT_B_label_n3 (n : ℕ) (hn : 4 ≤ n) :
    CoxeterMatrix.B n (⟨n-2, by omega⟩ : Fin n) (⟨n-3, by omega⟩ : Fin n) = 3 := by
  simp only [CoxeterMatrix.B, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem ggQ2xCT_Bcoex_eq_Acoex (n : ℕ) (p q : Fin n) (hp : (p:ℕ) + 3 ≤ n) :
    (CoxeterMatrix.B n) p q = (CoxeterMatrix.A n) p q := by
  have hn2 : 2 ≤ n := by omega
  simp only [CoxeterMatrix.B, CoxeterMatrix.A, Matrix.of_apply]
  split_ifs <;> omega

private theorem ggQ2xCT_B_label_bond (n : ℕ) (hn : 4 ≤ n) :
    CoxeterMatrix.B n (⟨n-2, by omega⟩ : Fin n) (⟨n-1, by omega⟩ : Fin n) = 4 := by
  haveI : NeZero n := ⟨by omega⟩
  have hne : n - 2 ≠ n - 1 := by omega
  have hne' : n - 1 ≠ n - 2 := by omega
  simp only [CoxeterMatrix.B, Matrix.of_apply, Fin.ext_iff, hne, hne']
  norm_num

private theorem ggQ2xCT_cartan_B_chainA (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hB : D.coxeter = (CoxeterMatrix.B n).reindex e) (p q : Fin n)
    (hp : (p:ℕ) + 3 ≤ n) : D.cartan (e p) (e q) = CartanMatrix.A n p q := by
  by_cases hpq : p = q
  · subst hpq
    rw [D.isCartan.1]
    simp [CartanMatrix.A]
  · have hne : e p ≠ e q := fun h => hpq (e.injective h)
    have hcox : D.coxeter (e p) (e q) = (CoxeterMatrix.A n) p q := by
      have h1 : D.coxeter (e p) (e q) = CoxeterMatrix.B n p q := by
        rw [hB, CoxeterMatrix.reindex_apply]; simp
      rw [h1, ggQ2xCT_Bcoex_eq_Acoex n p q hp]
    have hlabel : (CoxeterMatrix.A n) p q = 2 ∨ (CoxeterMatrix.A n) p q = 3 := by
      simp only [CoxeterMatrix.A, Matrix.of_apply]
      rw [if_neg hpq]
      by_cases h : (q : ℕ) + 1 = (p : ℕ) ∨ (p : ℕ) + 1 = (q : ℕ)
      · exact Or.inr (if_pos h)
      · exact Or.inl (if_neg h)
    rcases hlabel with h2 | h3
    · have hA0 : CartanMatrix.A n p q = 0 := by
        simp only [CartanMatrix.A, Matrix.of_apply, if_neg hpq]
        split_ifs with hh
        · exfalso
          have hcontra : (CoxeterMatrix.A n) p q = 3 := by
            simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hpq]
            exact if_pos (Or.symm hh)
          omega
        · rfl
      rcases D.isCartan.2 (e p) (e q) hne with ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ |
        ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · rw [h1, hA0]
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega
    · have hadj : (p : ℕ) + 1 = (q : ℕ) ∨ (q : ℕ) + 1 = (p : ℕ) := by
        by_contra hh
        have hcontra : (CoxeterMatrix.A n) p q = 2 := by
          simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hpq]
          exact if_neg (fun hD => hh (Or.symm hD))
        omega
      have hAneg : CartanMatrix.A n p q = -1 := by
        simp only [CartanMatrix.A, Matrix.of_apply, if_neg hpq]
        exact if_pos hadj
      rcases D.isCartan.2 (e p) (e q) hne with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ |
        ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · rw [hcox] at hm; omega
      · rw [h1, hAneg]
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega

private theorem ggQ2xCT_rowB (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hB : D.coxeter = (CoxeterMatrix.B n).reindex e) (c : D.ι → ZMod 3)
    (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) (p : Fin n)
    (hp : (p:ℕ) + 3 ≤ n) :
    (if h : (p:ℕ) + 1 < n then c (e (ggQ2xCT_succ p h)) else 0)
      + (if h : 0 < (p:ℕ) then c (e (ggQ2xCT_pred p)) else 0)
      = 2 * c (e p) := by
  have h := hc (e p)
  rw [← Equiv.sum_comp e (fun j => (D.cartan (e p) j : ZMod 3) * c j)] at h
  have h2 : (∑ q : Fin n, (D.cartan (e p) (e q) : ZMod 3) * c (e q))
      = ∑ q : Fin n, ggQ2xCT_Acoef p q * c (e q) := by
    apply Finset.sum_congr rfl
    intro q _
    rw [ggQ2xCT_cartan_B_chainA D e hB p q hp, ggQ2xCT_coefA p q]
  have hsum : (∑ q : Fin n, ggQ2xCT_Acoef p q * c (e q)) = 0 := by
    rw [← h2]
    exact h
  have hs := ggQ2xCT_sumA_plus p (fun q => c (e q))
  rw [hsum] at hs
  simpa using hs

private theorem ggQ2xCT_bt1 : ∀ A t y : ZMod 3,
    2 * y + (A * t) = 0 → 2 * (A * t) + 2 * ((A - 1) * t) + 2 * y = 0 → t = 0 := by
  decide +kernel

private theorem ggQ2xCT_bt2 : ∀ A t y : ZMod 3,
    2 * y + 2 * (A * t) = 0 → 2 * (A * t) + 2 * ((A - 1) * t) + y = 0 → t = 0 := by
  decide +kernel

private theorem ggQ2xCT_rowB_n1 (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hB : D.coxeter = (CoxeterMatrix.B n).reindex e) (c : D.ι → ZMod 3)
    (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) (hn : 4 ≤ n) :
    2 * c (e ⟨n-1, by omega⟩)
      + (((D.cartan (e ⟨n-1, by omega⟩) (e ⟨n-2, by omega⟩) : ℤ) : ZMod 3))
        * c (e ⟨n-2, by omega⟩) = 0 := by
  have h := hc (e ⟨n-1, by omega⟩)
  rw [← Equiv.sum_comp e (fun j => (D.cartan (e ⟨n-1, by omega⟩) j : ZMod 3) * c j)] at h
  have hcoef : ∀ q, (((D.cartan (e ⟨n-1, by omega⟩) (e q) : ℤ) : ZMod 3))
      = if q = (⟨n-1, by omega⟩ : Fin n) then 2
        else if q = (⟨n-2, by omega⟩ : Fin n) then
          (((D.cartan (e ⟨n-1, by omega⟩) (e ⟨n-2, by omega⟩) : ℤ) : ZMod 3))
        else 0 := by
    intro q
    by_cases h1 : q = (⟨n-1, by omega⟩ : Fin n)
    · rw [h1]
      rw [D.isCartan.1]
      norm_num
    · by_cases h2 : q = (⟨n-2, by omega⟩ : Fin n)
      · rw [if_neg h1, if_pos h2, h2]
      · rw [if_neg h1, if_neg h2]
        have hcox : D.coxeter (e ⟨n-1, by omega⟩) (e q) = 2 := by
          rw [hB, CoxeterMatrix.reindex_apply]
          simpa using ggQ2xCT_B_label_last n (by omega) q h1 h2
        rw [show D.cartan (e ⟨n-1, by omega⟩) (e q) = 0 from
          ggQ2xCT_label2 D (fun hh => h1 (e.injective hh).symm) hcox]
        norm_num
  rw [ggQ2xCT_sum_leaf_gen (fun q => ((D.cartan (e ⟨n-1, by omega⟩) (e q) : ℤ) : ZMod 3))
      (⟨n-1, by omega⟩ : Fin n) (⟨n-2, by omega⟩ : Fin n) (by
        intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_mk] at hv; omega)
      _ hcoef (fun q => c (e q))] at h
  exact h

private theorem ggQ2xCT_rowB_n2 (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hB : D.coxeter = (CoxeterMatrix.B n).reindex e) (c : D.ι → ZMod 3)
    (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) (hn : 4 ≤ n) :
    2 * c (e ⟨n-2, by omega⟩) + 2 * c (e ⟨n-3, by omega⟩)
      + (((D.cartan (e ⟨n-2, by omega⟩) (e ⟨n-1, by omega⟩) : ℤ) : ZMod 3))
        * c (e ⟨n-1, by omega⟩) = 0 := by
  have h := hc (e ⟨n-2, by omega⟩)
  rw [← Equiv.sum_comp e (fun j => (D.cartan (e ⟨n-2, by omega⟩) j : ZMod 3) * c j)] at h
  have hcoef : ∀ q, (((D.cartan (e ⟨n-2, by omega⟩) (e q) : ℤ) : ZMod 3))
      = if q = (⟨n-2, by omega⟩ : Fin n) then 2
        else if q = (⟨n-3, by omega⟩ : Fin n) then 2
        else if q = (⟨n-1, by omega⟩ : Fin n) then
          (((D.cartan (e ⟨n-2, by omega⟩) (e ⟨n-1, by omega⟩) : ℤ) : ZMod 3))
        else 0 := by
    intro q
    by_cases h1 : q = (⟨n-2, by omega⟩ : Fin n)
    · rw [h1]
      rw [D.isCartan.1]
      norm_num
    · by_cases h2 : q = (⟨n-3, by omega⟩ : Fin n)
      · rw [if_neg h1, if_pos h2, h2]
        have hcox : D.coxeter (e ⟨n-2, by omega⟩) (e ⟨n-3, by omega⟩) = 3 := by
          rw [hB, CoxeterMatrix.reindex_apply]
          simpa using ggQ2xCT_B_label_n3 n hn
        have hne23 : e ⟨n-2, by omega⟩ ≠ e ⟨n-3, by omega⟩ := by
          intro hh
          have hv := congrArg Fin.val (e.injective hh)
          simp only [Fin.val_mk] at hv
          omega
        rw [show D.cartan (e ⟨n-2, by omega⟩) (e ⟨n-3, by omega⟩) = -1 from
          ggQ2xCT_label3 D hne23 hcox]
        decide
      · by_cases h3 : q = (⟨n-1, by omega⟩ : Fin n)
        · rw [if_neg h1, if_neg h2, if_pos h3, h3]
        · rw [if_neg h1, if_neg h2, if_neg h3]
          have hcox : D.coxeter (e ⟨n-2, by omega⟩) (e q) = 2 := by
            rw [hB, CoxeterMatrix.reindex_apply]
            simpa using ggQ2xCT_B_label_n2 n hn q h1 h2 h3
          rw [show D.cartan (e ⟨n-2, by omega⟩) (e q) = 0 from
            ggQ2xCT_label2 D (fun hh => h1 (e.injective hh).symm) hcox]
          norm_num
  rw [ggQ2xCT_sum_leaf_gen3 (fun q => ((D.cartan (e ⟨n-2, by omega⟩) (e q) : ℤ) : ZMod 3))
      (⟨n-2, by omega⟩ : Fin n) (⟨n-3, by omega⟩ : Fin n) (⟨n-1, by omega⟩ : Fin n)
      (by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_mk] at hv; omega)
      (by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_mk] at hv; omega)
      (by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_mk] at hv; omega)
      _ hcoef (fun q => c (e q))] at h
  exact h

private theorem ggQ2xCT_kernel_B (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hB : D.coxeter = (CoxeterMatrix.B n).reindex e) (hn : 4 ≤ n)
    (c : D.ι → ZMod 3) (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) : c = 0 := by
  let d : ℕ → ZMod 3 := fun k => if h : k < n then c (e ⟨k, h⟩) else 0
  have hd : ∀ k (h : k < n), d k = c (e ⟨k, h⟩) := fun k h => by
    show (if h' : k < n then c (e ⟨k, h'⟩) else 0) = c (e ⟨k, h⟩)
    rw [dif_pos h]
  have hn0 : 0 < n := by omega
  have hp0 : ((⟨0, hn0⟩ : Fin n) : ℕ) + 3 ≤ n := by simp only [Fin.val_mk]; omega
  have h0 : 2 * d 0 = d 1 := by
    have hr := ggQ2xCT_rowB D e hB c hc (⟨0, hn0⟩ : Fin n) hp0
    rw [dif_pos (by omega : (0:ℕ) + 1 < n), dif_neg (Nat.lt_irrefl 0), add_zero] at hr
    rw [hd 0 hn0, hd 1 (by omega : 1 < n)]
    exact hr.symm
  have hstep : ∀ k, 1 ≤ k → k + 1 < n - 1 → d (k + 1) + d (k - 1) = 2 * d k := by
    intro k hk1 hk2
    have hk : k < n := by omega
    have hp : ((⟨k, hk⟩ : Fin n) : ℕ) + 3 ≤ n := by simp only [Fin.val_mk]; omega
    have hr := ggQ2xCT_rowB D e hB c hc (⟨k, hk⟩ : Fin n) hp
    rw [dif_pos (by omega : k + 1 < n), dif_pos (by omega : 0 < k)] at hr
    rw [hd (k + 1) (by omega), hd k hk, hd (k - 1) (by omega)]
    convert hr using 2 <;> exact Fin.ext rfl
  have hrec := ggQ2xCT_rec (n - 1) d h0 hstep
  have hx2 : c (e ⟨n-2, by omega⟩) = ((n-1:ℕ):ZMod 3) * d 0 := by
    rw [← hd (n-2) (by omega : n - 2 < n)]
    simpa only [show n - 2 + 1 = n - 1 by omega] using hrec (n - 2) (by omega)
  have hx3 : c (e ⟨n-3, by omega⟩) = ((n-2:ℕ):ZMod 3) * d 0 := by
    rw [← hd (n-3) (by omega : n - 3 < n)]
    simpa only [show n - 3 + 1 = n - 2 by omega] using hrec (n - 3) (by omega)
  have hBA : ((n-2:ℕ):ZMod 3) = ((n-1:ℕ):ZMod 3) - 1 := by
    rw [show n - 2 = n - 1 - 1 by omega, Nat.cast_sub (by omega : 1 ≤ n - 1), Nat.cast_one]
  have hn1 := ggQ2xCT_rowB_n1 D e hB c hc hn
  have hn2 := ggQ2xCT_rowB_n2 D e hB c hc hn
  have hlab : D.coxeter (e ⟨n-2, by omega⟩) (e ⟨n-1, by omega⟩) = 4 := by
    rw [hB, CoxeterMatrix.reindex_apply]
    simpa using ggQ2xCT_B_label_bond n hn
  have hne : e ⟨n-2, by omega⟩ ≠ e ⟨n-1, by omega⟩ :=
    e.injective.ne (by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega)
  rcases ggQ2xCT_label4 D hne hlab with ⟨hcd, hdc⟩ | ⟨hcd, hdc⟩
  · have hβ : (((D.cartan (e ⟨n-1, by omega⟩) (e ⟨n-2, by omega⟩) : ℤ) : ZMod 3)) = 1 := by
      rw [hdc]; decide
    have hγ : (((D.cartan (e ⟨n-2, by omega⟩) (e ⟨n-1, by omega⟩) : ℤ) : ZMod 3)) = 2 := by
      rw [hcd]; decide
    rw [hβ, hx2] at hn1
    rw [hγ, hx2, hx3, hBA] at hn2
    have ht : d 0 = 0 := ggQ2xCT_bt1 _ _ _ (by simpa using hn1) (by simpa using hn2)
    have hdz : ∀ k, k < n - 1 → d k = 0 := by
      intro k hk; rw [hrec k hk, ht, mul_zero]
    have hz2 : c (e ⟨n-2, by omega⟩) = 0 := by rw [hx2, ht, mul_zero]
    have hz1 : c (e ⟨n-1, by omega⟩) = 0 := by
      have hh := hn1
      simp only [ht, mul_zero, add_zero] at hh
      exact ggQ2xCT_two_zero _ hh
    funext i
    obtain ⟨k, rfl⟩ := e.surjective i
    by_cases hk : (k:ℕ) < n - 1
    · have hzero := hdz k hk
      rw [hd k k.isLt] at hzero
      exact hzero
    · have hk2 : (k:ℕ) = n - 1 := by omega
      have hki : k = (⟨n-1, by omega⟩ : Fin n) := Fin.ext hk2
      rw [hki]; exact hz1
  · have hβ : (((D.cartan (e ⟨n-1, by omega⟩) (e ⟨n-2, by omega⟩) : ℤ) : ZMod 3)) = 2 := by
      rw [hdc]; decide
    have hγ : (((D.cartan (e ⟨n-2, by omega⟩) (e ⟨n-1, by omega⟩) : ℤ) : ZMod 3)) = 1 := by
      rw [hcd]; decide
    rw [hβ, hx2] at hn1
    rw [hγ, hx2, hx3, hBA] at hn2
    have ht : d 0 = 0 := ggQ2xCT_bt2 _ _ _ (by simpa using hn1) (by simpa using hn2)
    have hdz : ∀ k, k < n - 1 → d k = 0 := by
      intro k hk; rw [hrec k hk, ht, mul_zero]
    have hz2 : c (e ⟨n-2, by omega⟩) = 0 := by rw [hx2, ht, mul_zero]
    have hz1 : c (e ⟨n-1, by omega⟩) = 0 := by
      have hh := hn1
      simp only [ht, mul_zero, add_zero] at hh
      exact ggQ2xCT_two_zero _ hh
    funext i
    obtain ⟨k, rfl⟩ := e.surjective i
    by_cases hk : (k:ℕ) < n - 1
    · have hzero := hdz k hk
      rw [hd k k.isLt] at hzero
      exact hzero
    · have hk2 : (k:ℕ) = n - 1 := by omega
      have hki : k = (⟨n-1, by omega⟩ : Fin n) := Fin.ext hk2
      rw [hki]; exact hz1

theorem ggQ2_caseII_relation (D : GGQ2Lin 3) (hII : D.CaseII) :
    ∃ c : D.ι → ZMod 3, (∑ k, c k • D.coroot k = 0) ∧ c D.a ≠ 0 ∧
      ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0 := by
  classical
  rcases Fintype.not_linearIndependent_iff.mp hII.2.2 with ⟨c, hc, i0, hi0⟩
  have hca : c D.a ≠ 0 := by
    intro hca0
    have hli := Fintype.linearIndependent_iff.mp hII.2.1
    have hsum0 : (∑ k : {k // k ≠ D.a}, c k.val • D.coroot k.val) = 0 := by
      have hfilter : (∑ k : {k // k ≠ D.a}, c k.val • D.coroot k.val)
          = ∑ k ∈ Finset.univ.filter (fun k => k ≠ D.a), c k • D.coroot k := by
        rw [← Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset D.ι))
          (f := fun k => c k • D.coroot k) (p := fun k => k ≠ D.a)]
        simp
      rw [hfilter]
      have : (∑ k ∈ Finset.univ.filter (fun k => k ≠ D.a), c k • D.coroot k)
          = ∑ k, c k • D.coroot k := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k = D.a
        · subst hk
          rw [if_neg (by simp), hca0, zero_smul]
        · rw [if_pos hk]
      rw [this, hc]
    have hzero : ∀ i, c i = 0 := by
      intro i
      by_cases hi : i = D.a
      · rw [hi]; exact hca0
      · exact hli (fun k => c k.val) hsum0 ⟨i, hi⟩
    exact hi0 (hzero i0)
  refine ⟨c, hc, hca, fun i => ?_⟩
  have happ : (∑ k, c k • D.root i (D.coroot k)) = 0 := by
    have h : (D.root i) (∑ k, c k • D.coroot k) = 0 := by rw [hc, map_zero]
    rw [map_sum] at h
    simpa only [map_smul] using h
  have hgoal : (∑ k, (D.cartan i k : ZMod 3) * c k)
      = ∑ k, c k • D.root i (D.coroot k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [D.pairing, smul_eq_mul, mul_comm]
  rw [hgoal, happ]

theorem ggQ2_caseII_kernel_A (D : GGQ2Lin 3) {m : ℕ} (e : Fin m ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A m).reindex e) (c : D.ι → ZMod 3)
    (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) (k : Fin m) :
    c (e k) = (((k : ℕ) + 1 : ℕ) : ZMod 3) * c (e ⟨0, Fin.pos k⟩) := by
  by_cases hm : m = 0
  · subst hm
    exact k.elim0
  have hm0 : 0 < m := Fin.pos k
  by_cases hm2 : 2 ≤ m
  · let d : ℕ → ZMod 3 := fun j => if h : j < m then c (e ⟨j, h⟩) else 0
    have hd : ∀ j (h : j < m), d j = c (e ⟨j, h⟩) := fun j h => by
      show (if h' : j < m then c (e ⟨j, h'⟩) else 0) = c (e ⟨j, h⟩)
      rw [dif_pos h]
    have h0 : 2 * d 0 = d 1 := by
      rw [hd 0 hm0, hd 1 (by omega : 1 < m)]
      exact ggQ2xCT_rowA_zero D e hA c hc hm0 hm2
    have hstep : ∀ j, 1 ≤ j → j + 1 < m → d (j + 1) + d (j - 1) = 2 * d j := by
      intro j hj1 hj2
      have hj : j < m := by omega
      have hmid := ggQ2xCT_rowA_mid D e hA c hc (⟨j, hj⟩ : Fin m) (by simpa using hj1)
        (by simpa using hj2)
      rw [hd (j + 1) (by omega : j + 1 < m), hd j hj, hd (j - 1) (by omega : j - 1 < m)]
      exact hmid
    have hrec := ggQ2xCT_rec m d h0 hstep k.val k.isLt
    rw [hd k.val k.isLt] at hrec
    rw [hd 0 hm0] at hrec
    have hdk : c (e k) = c (e ⟨k.val, k.isLt⟩) := by rfl
    rw [hdk, show (⟨0, Fin.pos k⟩ : Fin m) = (⟨0, hm0⟩ : Fin m) from Fin.ext rfl]
    exact hrec
  · have hm1 : m = 1 := by omega
    subst hm1
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    simp

theorem ggQ2_caseII_kernel_E6 (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (c : D.ι → ZMod 3)
    (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) :
    c (e 1) = 0 ∧ c (e 3) = 0 ∧ c (e 2) = 2 * c (e 0) ∧ c (e 4) = c (e 0) ∧
      c (e 5) = 2 * c (e 0) := by
  let d : Fin 6 → ZMod 3 := fun p => c (e p)
  have hrow : ∀ p : Fin 6,
      ∑ q : Fin 6, ((CartanMatrix.E 6 p q : ℤ) : ZMod 3) * d q = 0 := by
    intro p
    have h := hc (e p)
    rw [← Equiv.sum_comp e (fun j => (D.cartan (e p) j : ZMod 3) * c j)] at h
    have h2 : (∑ q : Fin 6, (D.cartan (e p) (e q) : ZMod 3) * c (e q))
        = ∑ q : Fin 6, ((CartanMatrix.E 6 p q : ℤ) : ZMod 3) * d q := by
      apply Finset.sum_congr rfl
      intro q _
      rw [ggQ2xCT_cartan_E6 D e hE p q]
    rw [h2] at h
    exact h
  exact ggQ2xCT_kernel_E6_dec d hrow

theorem ggQ2_caseII_types (D : GGQ2Lin 3) (hII : D.CaseII) (h4 : 4 ≤ Fintype.card D.ι) :
    (∃ (m : ℕ) (e : Fin m ≃ D.ι) (hm : 5 ≤ m), (m + 1) % 3 = 0 ∧
        D.coxeter = (CoxeterMatrix.A m).reindex e ∧
        (D.a = e ⟨0, by omega⟩ ∨ D.a = e ⟨m - 1, by omega⟩)) ∨
      (∃ e : Fin 6 ≃ D.ι, D.coxeter = CoxeterMatrix.E₆.reindex e ∧
        (D.a = e 0 ∨ D.a = e 5)) := by
  obtain ⟨c, hc0, hca, hc⟩ := ggQ2_caseII_relation D hII
  have hcard : ∀ {m : ℕ} (e : Fin m ≃ D.ι), m = Fintype.card D.ι := fun {m} e => by
    rw [← Fintype.card_fin m, Fintype.card_congr e]
  rcases D.isWeyl with ⟨m, e, hm1, hM⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG2⟩
  · rcases hM with hA | ⟨hm2, hB⟩ | ⟨hm4, hD⟩
    · have hme : m = Fintype.card D.ι := hcard e
      have hm4' : 4 ≤ m := by omega
      have hm0 : 0 < m := by omega
      have hc0_ne : c (e ⟨0, hm0⟩) ≠ 0 := by
        intro h0
        have hzero : ∀ k : Fin m, c (e k) = 0 := by
          intro k
          rw [ggQ2_caseII_kernel_A D e hA c hc k, h0, mul_zero]
        obtain ⟨k, hk⟩ := e.surjective D.a
        exact hca (by rw [← hk]; exact hzero k)
      have hlast : 2 * c (e ⟨m-1, by omega⟩) = c (e ⟨m-2, by omega⟩) := by
        have hr := ggQ2xCT_rowA D e hA c hc (⟨m-1, by omega⟩ : Fin m)
        rw [dif_neg (by omega : ¬ (m-1) + 1 < m), dif_pos (by omega : 0 < m-1),
          zero_add] at hr
        have hpred : ggQ2xCT_pred (⟨m-1, by omega⟩ : Fin m) = (⟨m-2, by omega⟩ : Fin m) := by
          apply Fin.ext; simp only [ggQ2xCT_pred]; omega
        rw [hpred] at hr
        exact hr.symm
      have hm1v : c (e ⟨m-1, by omega⟩) = ((m:ℕ):ZMod 3) * c (e ⟨0, hm0⟩) := by
        have := ggQ2_caseII_kernel_A D e hA c hc (⟨m-1, by omega⟩ : Fin m)
        simpa only [show m - 1 + 1 = m by omega] using this
      have hm2v : c (e ⟨m-2, by omega⟩) = ((m-1:ℕ):ZMod 3) * c (e ⟨0, hm0⟩) := by
        have ht := ggQ2_caseII_kernel_A D e hA c hc (⟨m-2, by omega⟩ : Fin m)
        rw [show m - 2 + 1 = m - 1 by omega] at ht
        simpa using ht
      have hrel : ((m+1:ℕ):ZMod 3) * c (e ⟨0, hm0⟩) = 0 := by
        rw [hm1v, hm2v] at hlast
        have hcast : ((m-1:ℕ):ZMod 3) = (m:ZMod 3) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
        rw [hcast] at hlast
        have hpoly : 2 * ((m:ZMod 3) * c (e ⟨0, hm0⟩))
            = ((m:ZMod 3) + 1) * c (e ⟨0, hm0⟩)
              + (((m:ZMod 3) - 1) * c (e ⟨0, hm0⟩)) := by ring
        rw [hpoly] at hlast
        have h0 : ((m:ZMod 3) + 1) * c (e ⟨0, hm0⟩) + (((m:ZMod 3) - 1) * c (e ⟨0, hm0⟩))
            = 0 + (((m:ZMod 3) - 1) * c (e ⟨0, hm0⟩)) := by rw [zero_add]; exact hlast
        have hres := add_right_cancel h0
        have hcast2 : ((m+1:ℕ):ZMod 3) = (m:ZMod 3) + 1 := by push_cast; ring
        rw [hcast2]
        exact hres
      have hzero3 : ((m+1:ℕ):ZMod 3) = 0 := (mul_eq_zero.mp hrel).resolve_right hc0_ne
      have hmod : (m + 1) % 3 = 0 :=
        Nat.dvd_iff_mod_eq_zero.mp ((CharP.cast_eq_zero_iff (ZMod 3) 3 (m+1)).mp hzero3)
      have hm5 : 5 ≤ m := by
        rcases (CharP.cast_eq_zero_iff (ZMod 3) 3 (m+1)).mp hzero3 with ⟨k, hk⟩
        omega
      left
      refine ⟨m, e, hm5, hmod, hA, ?_⟩
      rcases D.a_leaf with ⟨w, ⟨hwna, hwcart⟩, hwuniq⟩
      obtain ⟨k, hk⟩ := e.surjective D.a
      have hneigh : ∀ q : Fin m, q ≠ k → D.cartan (e k) (e q) ≠ 0 → e q = w := by
        intro q hq hcq
        apply hwuniq
        refine ⟨?_, ?_⟩
        · rw [← hk]; intro hh; exact hq (e.injective hh)
        · rw [← hk]; exact hcq
      have hkend : (k:ℕ) = 0 ∨ (k:ℕ) + 1 = m := by
        by_contra h
        push Not at h
        obtain ⟨hk0, hkm⟩ := h
        have hkpos : 1 ≤ (k:ℕ) := by omega
        have hklt : (k:ℕ) + 1 < m := by omega
        have hklt' : (k:ℕ) - 1 < m := by omega
        have hc1 : D.cartan (e k) (e ⟨(k:ℕ)+1, hklt⟩) ≠ 0 := by
          rw [ggQ2xCT_cartan_A D e hA k ⟨(k:ℕ)+1, hklt⟩]
          simp only [CartanMatrix.A, Matrix.of_apply]
          rw [if_neg (by
            intro hh
            have hv := congrArg Fin.val hh
            simp only [Fin.val_mk] at hv
            omega)]
          simp
        have hc2 : D.cartan (e k) (e ⟨(k:ℕ)-1, hklt'⟩) ≠ 0 := by
          rw [ggQ2xCT_cartan_A D e hA k ⟨(k:ℕ)-1, hklt'⟩]
          simp only [CartanMatrix.A, Matrix.of_apply]
          rw [if_neg (by
            intro hh
            have hv := congrArg Fin.val hh
            simp only [Fin.val_mk] at hv
            omega)]
          omega
        have hq1 : (⟨(k:ℕ)+1, hklt⟩ : Fin m) ≠ k := by
          intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_mk] at hv; omega
        have hq2 : (⟨(k:ℕ)-1, hklt'⟩ : Fin m) ≠ k := by
          intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_mk] at hv; omega
        have h1 := hneigh ⟨(k:ℕ)+1, hklt⟩ hq1 hc1
        have h2 := hneigh ⟨(k:ℕ)-1, hklt'⟩ hq2 hc2
        have heq : (⟨(k:ℕ)+1, hklt⟩ : Fin m) = ⟨(k:ℕ)-1, hklt'⟩ := e.injective (h1.trans h2.symm)
        have hv := congrArg Fin.val heq
        simp only [Fin.val_mk] at hv
        omega
      rcases hkend with hk0 | hkm
      · left
        rw [← hk]; congr 1; apply Fin.ext; simp only [Fin.val_mk]; omega
      · right
        rw [← hk]; congr 1; apply Fin.ext; simp only [Fin.val_mk]; omega
    · exfalso
      have hm4' : 4 ≤ m := by have := hcard e; omega
      exact hca (congrFun (ggQ2xCT_kernel_B D e hB hm4' c hc) D.a)
    · exfalso
      exact hca (congrFun (ggQ2xCT_kernel_D D e hD hm4 c hc) D.a)
  · obtain ⟨hk1, hk3, hk2, hk4, hk5⟩ := ggQ2_caseII_kernel_E6 D e hE6 c hc
    have hc0_ne : c (e 0) ≠ 0 := by
      intro h0
      have hzero : ∀ k : Fin 6, c (e k) = 0 := by
        intro k; fin_cases k <;> simp_all
      obtain ⟨k, hk⟩ := e.surjective D.a
      exact hca (by rw [← hk]; exact hzero k)
    rcases D.a_leaf with ⟨w, ⟨hwna, hwcart⟩, hwuniq⟩
    obtain ⟨k, hk⟩ := e.surjective D.a
    have hck : c (e k) ≠ 0 := by rw [hk]; exact hca
    have hneigh : ∀ q : Fin 6, q ≠ k → D.cartan (e k) (e q) ≠ 0 → e q = w := by
      intro q hq hcq
      apply hwuniq
      refine ⟨?_, ?_⟩
      · rw [← hk]; intro hh; exact hq (e.injective hh)
      · rw [← hk]; exact hcq
    have hk1' : k ≠ 1 := by intro h; subst h; exact hck hk1
    have hkleaf : k = 0 ∨ k = 5 := by
      fin_cases k
      · exact Or.inl rfl
      · exact absurd rfl hk1'
      · exfalso
        have h20 : D.cartan (e 2) (e 0) ≠ 0 := by
          rw [ggQ2xCT_cartan_E6 D e hE6 2 0]; decide
        have h23 : D.cartan (e 2) (e 3) ≠ 0 := by
          rw [ggQ2xCT_cartan_E6 D e hE6 2 3]; decide
        have h1 := hneigh 0 (by decide) h20
        have h2 := hneigh 3 (by decide) h23
        have := congrArg Fin.val (e.injective (h1.trans h2.symm)); simp at this
      · exfalso
        have h31 : D.cartan (e 3) (e 1) ≠ 0 := by
          rw [ggQ2xCT_cartan_E6 D e hE6 3 1]; decide
        have h32 : D.cartan (e 3) (e 2) ≠ 0 := by
          rw [ggQ2xCT_cartan_E6 D e hE6 3 2]; decide
        have h1 := hneigh 1 (by decide) h31
        have h2 := hneigh 2 (by decide) h32
        have := congrArg Fin.val (e.injective (h1.trans h2.symm)); simp at this
      · exfalso
        have h43 : D.cartan (e 4) (e 3) ≠ 0 := by
          rw [ggQ2xCT_cartan_E6 D e hE6 4 3]; decide
        have h45 : D.cartan (e 4) (e 5) ≠ 0 := by
          rw [ggQ2xCT_cartan_E6 D e hE6 4 5]; decide
        have h1 := hneigh 3 (by decide) h43
        have h2 := hneigh 5 (by decide) h45
        have := congrArg Fin.val (e.injective (h1.trans h2.symm)); simp at this
      · exact Or.inr rfl
    right
    refine ⟨e, hE6, ?_⟩
    rcases hkleaf with hk0 | hk5
    · left; rw [← hk, hk0]
    · right; rw [← hk, hk5]
  · exfalso
    have hCc := ggQ2xCT_cartan_E7 D e hE7
    exact hca (congrFun
      (ggQ2xCT_kernel_of_reindex D e (CartanMatrix.E 7) hCc c hc ggQ2xCT_kernel_E7_dec) D.a)
  · exfalso
    have hCc := ggQ2xCT_cartan_E8 D e hE8
    exact hca (congrFun
      (ggQ2xCT_kernel_of_reindex D e (CartanMatrix.E 8) hCc c hc ggQ2xCT_kernel_E8_dec) D.a)
  · exfalso
    exact hca (congrFun (ggQ2xCT_kernel_F4 D e hF4 c hc) D.a)
  · exfalso
    have h2 : 2 = Fintype.card D.ι := hcard e
    omega

theorem ggQ2_caseII_cartan_symm (D : GGQ2Lin 3) (hII : D.CaseII) (h4 : 4 ≤ Fintype.card D.ι) :
    ∀ i j, D.cartan i j = D.cartan j i := by
  rcases ggQ2_caseII_types D hII h4 with ⟨m, e, hm, hmod, hA, -⟩ | ⟨e, hE6, -⟩
  · intro i j
    by_cases hij : i = j
    · rw [hij]
    · obtain ⟨p, rfl⟩ := e.surjective i
      obtain ⟨q, rfl⟩ := e.surjective j
      rw [ggQ2xCT_cartan_A D e hA p q, ggQ2xCT_cartan_A D e hA q p]
      simp [CartanMatrix.A, Matrix.of_apply, eq_comm, or_comm]
  · intro i j
    by_cases hij : i = j
    · rw [hij]
    · obtain ⟨p, rfl⟩ := e.surjective i
      obtain ⟨q, rfl⟩ := e.surjective j
      rw [ggQ2xCT_cartan_E6 D e hE6 p q, ggQ2xCT_cartan_E6 D e hE6 q p]
      exact congrFun (congrFun (CartanMatrix.E_transpose 6) q) p

end CFSG.StandardType

end

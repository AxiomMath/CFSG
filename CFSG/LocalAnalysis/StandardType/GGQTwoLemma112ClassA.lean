module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112K

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggQ2xKD_ClassHyp (n : ℕ) (C : Matrix (Fin n) (Fin n) ℤ) (a₀ : Fin n) : Prop :=
  (∃! c, c ≠ a₀ ∧ C a₀ c ≠ 0) ∧ 3 ≤ n - 1 ∧
    ∃ κ : {i : Fin n // i ≠ a₀} → ZMod 3, κ ≠ 0 ∧
      ∀ i : {i : Fin n // i ≠ a₀}, ∑ j : {i : Fin n // i ≠ a₀}, ((C i j : ℤ) : ZMod 3) * κ j = 0

@[expose] def ggQ2xKD_ClassConcl (n : ℕ) (C : Matrix (Fin n) (Fin n) ℤ) (a₀ : Fin n) : Prop :=
  (∃ k : ℕ, 2 ≤ k ∧ ∃ e : Fin (3 * k - 1) ≃ {i : Fin n // i ≠ a₀},
      ∀ i j, C (e i) (e j) = CartanMatrix.A (3 * k - 1) i j) ∨
    (∃ e : Fin 6 ≃ {i : Fin n // i ≠ a₀}, ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j)

private lemma ggQ2xKDd_A_succ (m : ℕ) (i j : Fin m) :
    CartanMatrix.A (m + 1) (Fin.succ i) (Fin.succ j) = CartanMatrix.A m i j := by
  rw [CartanMatrix.A, CartanMatrix.A, Matrix.of_apply, Matrix.of_apply]
  simp only [Fin.val_succ, Fin.succ_inj]
  split_ifs <;> omega

private lemma ggQ2xKDd_A_castSucc (m : ℕ) (i j : Fin m) :
    CartanMatrix.A (m + 1) (Fin.castSucc i) (Fin.castSucc j) = CartanMatrix.A m i j := by
  rw [CartanMatrix.A, CartanMatrix.A, Matrix.of_apply, Matrix.of_apply]
  simp only [Fin.val_castSucc, Fin.castSucc_inj]

private lemma ggQ2xKDd_A_cast {m n : ℕ} (h : m = n) (i j : Fin m) :
    CartanMatrix.A n (Fin.cast h i) (Fin.cast h j) = CartanMatrix.A m i j := by
  subst h
  rfl

private lemma ggQ2xKDd_A_prev {n : ℕ} {i j : Fin n} (hij : j.val + 1 = i.val) :
    CartanMatrix.A n i j = -1 := by
  have hne : i ≠ j := by intro h'; rw [h'] at hij; omega
  rw [CartanMatrix.A, Matrix.of_apply]
  rw [if_neg hne, if_pos (Or.inr hij)]

private lemma ggQ2xKDd_A_next {n : ℕ} {i j : Fin n} (hij : i.val + 1 = j.val) :
    CartanMatrix.A n i j = -1 := by
  have hne : i ≠ j := by intro h'; rw [h'] at hij; omega
  rw [CartanMatrix.A, Matrix.of_apply]
  rw [if_neg hne, if_pos (Or.inl hij)]

lemma ggQ2xKDd_leaf_of_row {n : ℕ} (hn : 2 ≤ n) (M : Matrix (Fin n) (Fin n) ℤ)
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

@[expose] noncomputable def ggQ2xKDd_succAboveEquiv (m : ℕ) (p : Fin (m + 1)) :
    Fin m ≃ {i : Fin (m + 1) // i ≠ p} :=
  Equiv.ofBijective
    (fun i => (⟨p.succAbove i, p.succAbove_ne i⟩ : {i : Fin (m + 1) // i ≠ p}))
    ⟨fun _ _ hij => Fin.succAbove_right_injective (congrArg Subtype.val hij), fun y => by
      obtain ⟨i, hi⟩ := show y.1 ∈ Set.range p.succAbove from by
        rw [Fin.range_succAbove]; exact y.2
      exact ⟨i, Subtype.ext hi⟩⟩

@[expose] noncomputable def ggQ2xKDd_complEquiv {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n) :
    Fin (n - 1) ≃ {i : Fin n // i ≠ a₀} :=
  (ggQ2xKDd_succAboveEquiv (n - 1) (Fin.cast (Nat.sub_add_cancel hn).symm a₀)).trans
    (Equiv.subtypeEquiv (finCongr (Nat.sub_add_cancel hn)) (fun i => by
      have hkey : finCongr (Nat.sub_add_cancel hn) (Fin.cast (Nat.sub_add_cancel hn).symm a₀)
          = a₀ := by simp
      constructor
      · intro h he
        apply h
        simpa using congrArg (Fin.cast (Nat.sub_add_cancel hn).symm) he
      · intro h he
        exact h (by rw [he]; exact hkey)))

theorem ggQ2xKDd_submatrix_det_zero {n m : ℕ} (N : Matrix (Fin n) (Fin n) ℤ)
    (a₀ : Fin n) (κ : {i : Fin n // i ≠ a₀} → ZMod 3) (hκne : κ ≠ 0)
    (hκeq : ∀ i : {i : Fin n // i ≠ a₀},
      ∑ j : {i : Fin n // i ≠ a₀}, ((N i j : ℤ) : ZMod 3) * κ j = 0)
    (e : Fin m ≃ {i : Fin n // i ≠ a₀}) (M : Matrix (Fin m) (Fin m) ℤ)
    (he : ∀ i j : Fin m, N (e i) (e j) = M i j) :
    (((Int.castRingHom (ZMod 3)).mapMatrix M)).det = 0 := by
  let κ' : Fin m → ZMod 3 := fun i => κ (e i)
  have hκ'ne : κ' ≠ 0 := by
    intro hz
    apply hκne
    funext y
    conv_lhs => rw [← e.apply_symm_apply y]
    exact congrFun hz (e.symm y)
  have hMv : Matrix.mulVec ((Int.castRingHom (ZMod 3)).mapMatrix M) κ' = 0 := by
    funext i
    have hi := hκeq (e i)
    rw [← Equiv.sum_comp e (fun j : {i : Fin n // i ≠ a₀} =>
      ((N (e i) j : ℤ) : ZMod 3) * κ j)] at hi
    change ∑ x, (Int.castRingHom (ZMod 3)) (M i x) * κ (e x) = 0
    rw [← hi]
    exact Finset.sum_congr rfl (fun j _ => by rw [he i j]; rfl)
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨κ', hκ'ne, hMv⟩

lemma ggQ2xKDd_A_det_apply (m : ℕ) :
    ((Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.A m)).det = ((m + 1 : ℕ) : ZMod 3) := by
  rw [← RingHom.map_det, CartanMatrix.A_det]
  push_cast
  norm_num

private theorem ggQ2xKDd_A_witness {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n)
    (h : a₀.val = 0 ∨ a₀.val = n - 1) :
    ∃ e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀},
      ∀ i j : Fin (n - 1),
        CartanMatrix.A n (e i) (e j) = CartanMatrix.A (n - 1) i j := by
  have hcast : n - 1 + 1 = n := Nat.sub_add_cancel hn
  let p : Fin (n - 1 + 1) := Fin.cast hcast.symm a₀
  let e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀} := ggQ2xKDd_complEquiv hn a₀
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
    rw [hi, hj, ggQ2xKDd_A_cast hcast]
    exact ggQ2xKDd_A_succ (n - 1) i j
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
    rw [hi, hj, ggQ2xKDd_A_cast hcast]
    exact ggQ2xKDd_A_castSucc (n - 1) i j

private theorem ggQ2xKDd_A_dvd {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n)
    (h : a₀.val = 0 ∨ a₀.val = n - 1) (κ : {i : Fin n // i ≠ a₀} → ZMod 3) (hκne : κ ≠ 0)
    (hκeq : ∀ i : {i : Fin n // i ≠ a₀},
      ∑ j : {i : Fin n // i ≠ a₀}, ((CartanMatrix.A n i j : ℤ) : ZMod 3) * κ j = 0) :
    3 ∣ n := by
  obtain ⟨e, hentries⟩ := ggQ2xKDd_A_witness hn a₀ h
  have hdet := ggQ2xKDd_submatrix_det_zero (CartanMatrix.A n) a₀ κ hκne hκeq e
    (CartanMatrix.A (n - 1)) hentries
  have hAdet := ggQ2xKDd_A_det_apply (n - 1)
  rw [Nat.sub_add_cancel hn] at hAdet
  have hnzero : (n : ZMod 3) = 0 := by
    rw [← hAdet]
    exact hdet
  exact (ZMod.natCast_eq_zero_iff n 3).mp hnzero

theorem ggQ2xKD_class_A {n : ℕ} (a₀ : Fin n)
    (h : ggQ2xKD_ClassHyp n (CartanMatrix.A n) a₀) :
    ggQ2xKD_ClassConcl n (CartanMatrix.A n) a₀ := by
  obtain ⟨hleaf, hn3, κ, hκne, hκeq⟩ := h
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hleaf' : a₀.val = 0 ∨ a₀.val = n - 1 :=
    ggQ2xKDd_leaf_of_row hn2 (CartanMatrix.A n) a₀
      (fun hij => by rw [ggQ2xKDd_A_prev hij]; decide)
      (fun hij => by rw [ggQ2xKDd_A_next hij]; decide) hleaf
  obtain ⟨e, hentries⟩ := ggQ2xKDd_A_witness hn1 a₀ hleaf'
  have hdvd : 3 ∣ n := ggQ2xKDd_A_dvd hn1 a₀ hleaf' κ hκne hκeq
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : 2 ≤ k := by omega
  subst hk
  exact Or.inl ⟨k, hk2, e, hentries⟩
end CFSG.StandardType

end

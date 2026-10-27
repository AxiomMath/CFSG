module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112ClassA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggQ2xKDd_B_prev {n : ℕ} {i j : Fin n} (hij : j.val + 1 = i.val) :
    CartanMatrix.B n i j ≠ 0 := by
  have hne : i ≠ j := by intro h'; rw [h'] at hij; omega
  rw [CartanMatrix.B, Matrix.of_apply]
  rw [if_neg hne, if_neg (by omega), if_pos hij]
  decide

private lemma ggQ2xKDd_B_next {n : ℕ} {i j : Fin n} (hij : i.val + 1 = j.val) :
    CartanMatrix.B n i j ≠ 0 := by
  have hne : i ≠ j := by intro h'; rw [h'] at hij; omega
  rw [CartanMatrix.B, Matrix.of_apply]
  rw [if_neg hne, if_pos hij]
  split_ifs <;> decide

private lemma ggQ2xKDd_B_succ (m : ℕ) (i j : Fin m) :
    CartanMatrix.B (m + 1) (Fin.succ i) (Fin.succ j) = CartanMatrix.B m i j := by
  rw [CartanMatrix.B, CartanMatrix.B, Matrix.of_apply, Matrix.of_apply]
  simp only [Fin.val_succ, Fin.succ_inj]
  split_ifs <;> omega

private lemma ggQ2xKDd_B_castSucc (m : ℕ) (i j : Fin m) :
    CartanMatrix.B (m + 1) (Fin.castSucc i) (Fin.castSucc j) = CartanMatrix.A m i j := by
  rw [CartanMatrix.B, CartanMatrix.A, Matrix.of_apply, Matrix.of_apply]
  simp only [Fin.val_castSucc, Fin.castSucc_inj]
  split_ifs <;> omega

private lemma ggQ2xKDd_B_cast {m n : ℕ} (h : m = n) (i j : Fin m) :
    CartanMatrix.B n (Fin.cast h i) (Fin.cast h j) = CartanMatrix.B m i j := by
  subst h
  rfl

private lemma ggQ2xKDd_C_prev {n : ℕ} {i j : Fin n} (hij : j.val + 1 = i.val) :
    CartanMatrix.C n i j ≠ 0 := by
  have hne : i ≠ j := by intro h'; rw [h'] at hij; omega
  rw [CartanMatrix.C, Matrix.of_apply]
  rw [if_neg hne, if_neg (by omega), if_pos hij]
  split_ifs <;> decide

private lemma ggQ2xKDd_C_next {n : ℕ} {i j : Fin n} (hij : i.val + 1 = j.val) :
    CartanMatrix.C n i j ≠ 0 := by
  have hne : i ≠ j := by intro h'; rw [h'] at hij; omega
  rw [CartanMatrix.C, Matrix.of_apply]
  rw [if_neg hne, if_pos hij]
  decide

private lemma ggQ2xKDd_C_succ (m : ℕ) (i j : Fin m) :
    CartanMatrix.C (m + 1) (Fin.succ i) (Fin.succ j) = CartanMatrix.C m i j := by
  rw [CartanMatrix.C, CartanMatrix.C, Matrix.of_apply, Matrix.of_apply]
  simp only [Fin.val_succ, Fin.succ_inj]
  split_ifs <;> omega

private lemma ggQ2xKDd_C_castSucc (m : ℕ) (i j : Fin m) :
    CartanMatrix.C (m + 1) (Fin.castSucc i) (Fin.castSucc j) = CartanMatrix.A m i j := by
  rw [CartanMatrix.C, CartanMatrix.A, Matrix.of_apply, Matrix.of_apply]
  simp only [Fin.val_castSucc, Fin.castSucc_inj]
  split_ifs <;> omega

private lemma ggQ2xKDd_C_cast {m n : ℕ} (h : m = n) (i j : Fin m) :
    CartanMatrix.C n (Fin.cast h i) (Fin.cast h j) = CartanMatrix.C m i j := by
  subst h
  rfl

private lemma ggQ2xKDd_B_det_apply (m : ℕ) (hm : 0 < m) :
    ((Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.B m)).det = 2 := by
  rw [← RingHom.map_det, CartanMatrix.B_det hm]
  norm_num

private lemma ggQ2xKDd_C_det_apply (m : ℕ) (hm : 0 < m) :
    ((Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.C m)).det = 2 := by
  rw [← RingHom.map_det, CartanMatrix.C_det hm]
  norm_num

private theorem ggQ2xKDd_B_witness {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n)
    (h : a₀.val = n - 1) :
    ∃ e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀},
      ∀ i j : Fin (n - 1),
        CartanMatrix.B n (e i) (e j) = CartanMatrix.A (n - 1) i j := by
  have hcast : n - 1 + 1 = n := Nat.sub_add_cancel hn
  let p : Fin (n - 1 + 1) := Fin.cast hcast.symm a₀
  let e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀} := ggQ2xKDd_complEquiv hn a₀
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
  rw [hi, hj, ggQ2xKDd_B_cast hcast]
  exact ggQ2xKDd_B_castSucc (n - 1) i j

private theorem ggQ2xKDd_B_zero_witness {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n)
    (h : a₀.val = 0) :
    ∃ e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀},
      ∀ i j : Fin (n - 1),
        CartanMatrix.B n (e i) (e j) = CartanMatrix.B (n - 1) i j := by
  have hcast : n - 1 + 1 = n := Nat.sub_add_cancel hn
  let p : Fin (n - 1 + 1) := Fin.cast hcast.symm a₀
  let e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀} := ggQ2xKDd_complEquiv hn a₀
  have he_val : ∀ i : Fin (n - 1), (e i).val = finCongr hcast (p.succAbove i) := fun i => rfl
  have hp : p = 0 := by ext; simp [p, h]
  refine ⟨e, fun i j => ?_⟩
  have hi : (e i).val = Fin.cast hcast (Fin.succ i) := by
    rw [he_val, hp, Fin.succAbove_zero]
    simp
  have hj : (e j).val = Fin.cast hcast (Fin.succ j) := by
    rw [he_val, hp, Fin.succAbove_zero]
    simp
  rw [hi, hj, ggQ2xKDd_B_cast hcast]
  exact ggQ2xKDd_B_succ (n - 1) i j

private theorem ggQ2xKDd_C_witness {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n)
    (h : a₀.val = n - 1) :
    ∃ e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀},
      ∀ i j : Fin (n - 1),
        CartanMatrix.C n (e i) (e j) = CartanMatrix.A (n - 1) i j := by
  have hcast : n - 1 + 1 = n := Nat.sub_add_cancel hn
  let p : Fin (n - 1 + 1) := Fin.cast hcast.symm a₀
  let e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀} := ggQ2xKDd_complEquiv hn a₀
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
  rw [hi, hj, ggQ2xKDd_C_cast hcast]
  exact ggQ2xKDd_C_castSucc (n - 1) i j

private theorem ggQ2xKDd_C_zero_witness {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n)
    (h : a₀.val = 0) :
    ∃ e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀},
      ∀ i j : Fin (n - 1),
        CartanMatrix.C n (e i) (e j) = CartanMatrix.C (n - 1) i j := by
  have hcast : n - 1 + 1 = n := Nat.sub_add_cancel hn
  let p : Fin (n - 1 + 1) := Fin.cast hcast.symm a₀
  let e : Fin (n - 1) ≃ {i : Fin n // i ≠ a₀} := ggQ2xKDd_complEquiv hn a₀
  have he_val : ∀ i : Fin (n - 1), (e i).val = finCongr hcast (p.succAbove i) := fun i => rfl
  have hp : p = 0 := by ext; simp [p, h]
  refine ⟨e, fun i j => ?_⟩
  have hi : (e i).val = Fin.cast hcast (Fin.succ i) := by
    rw [he_val, hp, Fin.succAbove_zero]
    simp
  have hj : (e j).val = Fin.cast hcast (Fin.succ j) := by
    rw [he_val, hp, Fin.succAbove_zero]
    simp
  rw [hi, hj, ggQ2xKDd_C_cast hcast]
  exact ggQ2xKDd_C_succ (n - 1) i j

private theorem ggQ2xKDd_B_dvd {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n) (h : a₀.val = n - 1)
    (κ : {i : Fin n // i ≠ a₀} → ZMod 3) (hκne : κ ≠ 0)
    (hκeq : ∀ i : {i : Fin n // i ≠ a₀},
      ∑ j : {i : Fin n // i ≠ a₀}, ((CartanMatrix.B n i j : ℤ) : ZMod 3) * κ j = 0) :
    3 ∣ n := by
  obtain ⟨e, hentries⟩ := ggQ2xKDd_B_witness hn a₀ h
  have hdet := ggQ2xKDd_submatrix_det_zero (CartanMatrix.B n) a₀ κ hκne hκeq e
    (CartanMatrix.A (n - 1)) hentries
  have hAdet := ggQ2xKDd_A_det_apply (n - 1)
  rw [Nat.sub_add_cancel hn] at hAdet
  have hnzero : (n : ZMod 3) = 0 := by
    rw [← hAdet]
    exact hdet
  exact (ZMod.natCast_eq_zero_iff n 3).mp hnzero

private theorem ggQ2xKDd_B_zero_contra {n : ℕ} (hn : 2 ≤ n) (a₀ : Fin n) (h : a₀.val = 0)
    (κ : {i : Fin n // i ≠ a₀} → ZMod 3) (hκne : κ ≠ 0)
    (hκeq : ∀ i : {i : Fin n // i ≠ a₀},
      ∑ j : {i : Fin n // i ≠ a₀}, ((CartanMatrix.B n i j : ℤ) : ZMod 3) * κ j = 0) :
    False := by
  have hn1 : 0 < n - 1 := Nat.sub_pos_of_lt (by omega)
  obtain ⟨e, hentries⟩ := ggQ2xKDd_B_zero_witness (by omega) a₀ h
  have hdet := ggQ2xKDd_submatrix_det_zero (CartanMatrix.B n) a₀ κ hκne hκeq e
    (CartanMatrix.B (n - 1)) hentries
  have hBdet := ggQ2xKDd_B_det_apply (n - 1) hn1
  rw [hBdet] at hdet
  exact absurd hdet (by decide)

private theorem ggQ2xKDd_C_dvd {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n) (h : a₀.val = n - 1)
    (κ : {i : Fin n // i ≠ a₀} → ZMod 3) (hκne : κ ≠ 0)
    (hκeq : ∀ i : {i : Fin n // i ≠ a₀},
      ∑ j : {i : Fin n // i ≠ a₀}, ((CartanMatrix.C n i j : ℤ) : ZMod 3) * κ j = 0) :
    3 ∣ n := by
  obtain ⟨e, hentries⟩ := ggQ2xKDd_C_witness hn a₀ h
  have hdet := ggQ2xKDd_submatrix_det_zero (CartanMatrix.C n) a₀ κ hκne hκeq e
    (CartanMatrix.A (n - 1)) hentries
  have hAdet := ggQ2xKDd_A_det_apply (n - 1)
  rw [Nat.sub_add_cancel hn] at hAdet
  have hnzero : (n : ZMod 3) = 0 := by
    rw [← hAdet]
    exact hdet
  exact (ZMod.natCast_eq_zero_iff n 3).mp hnzero

private theorem ggQ2xKDd_C_zero_contra {n : ℕ} (hn : 2 ≤ n) (a₀ : Fin n) (h : a₀.val = 0)
    (κ : {i : Fin n // i ≠ a₀} → ZMod 3) (hκne : κ ≠ 0)
    (hκeq : ∀ i : {i : Fin n // i ≠ a₀},
      ∑ j : {i : Fin n // i ≠ a₀}, ((CartanMatrix.C n i j : ℤ) : ZMod 3) * κ j = 0) :
    False := by
  have hn1 : 0 < n - 1 := Nat.sub_pos_of_lt (by omega)
  obtain ⟨e, hentries⟩ := ggQ2xKDd_C_zero_witness (by omega) a₀ h
  have hdet := ggQ2xKDd_submatrix_det_zero (CartanMatrix.C n) a₀ κ hκne hκeq e
    (CartanMatrix.C (n - 1)) hentries
  have hCdet := ggQ2xKDd_C_det_apply (n - 1) hn1
  rw [hCdet] at hdet
  exact absurd hdet (by decide)

theorem ggQ2xKD_class_B {n : ℕ} (a₀ : Fin n)
    (h : ggQ2xKD_ClassHyp n (CartanMatrix.B n) a₀) :
    ggQ2xKD_ClassConcl n (CartanMatrix.B n) a₀ := by
  obtain ⟨hleaf, hn3, κ, hκne, hκeq⟩ := h
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hleaf' : a₀.val = 0 ∨ a₀.val = n - 1 :=
    ggQ2xKDd_leaf_of_row hn2 (CartanMatrix.B n) a₀
      (fun hij => ggQ2xKDd_B_prev hij) (fun hij => ggQ2xKDd_B_next hij) hleaf
  rcases hleaf' with h0 | hlast
  · exact absurd (ggQ2xKDd_B_zero_contra hn2 a₀ h0 κ hκne hκeq) (by simp)
  · obtain ⟨e, hentries⟩ := ggQ2xKDd_B_witness hn1 a₀ hlast
    have hdvd : 3 ∣ n := ggQ2xKDd_B_dvd hn1 a₀ hlast κ hκne hκeq
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : 2 ≤ k := by omega
    subst hk
    exact Or.inl ⟨k, hk2, e, hentries⟩

theorem ggQ2xKD_class_C {n : ℕ} (a₀ : Fin n)
    (h : ggQ2xKD_ClassHyp n (CartanMatrix.C n) a₀) :
    ggQ2xKD_ClassConcl n (CartanMatrix.C n) a₀ := by
  obtain ⟨hleaf, hn3, κ, hκne, hκeq⟩ := h
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hleaf' : a₀.val = 0 ∨ a₀.val = n - 1 :=
    ggQ2xKDd_leaf_of_row hn2 (CartanMatrix.C n) a₀
      (fun hij => ggQ2xKDd_C_prev hij) (fun hij => ggQ2xKDd_C_next hij) hleaf
  rcases hleaf' with h0 | hlast
  · exact absurd (ggQ2xKDd_C_zero_contra hn2 a₀ h0 κ hκne hκeq) (by simp)
  · obtain ⟨e, hentries⟩ := ggQ2xKDd_C_witness hn1 a₀ hlast
    have hdvd : 3 ∣ n := ggQ2xKDd_C_dvd hn1 a₀ hlast κ hκne hκeq
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : 2 ≤ k := by omega
    subst hk
    exact Or.inl ⟨k, hk2, e, hentries⟩
end CFSG.StandardType

end

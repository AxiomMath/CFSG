module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112ClassA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def ggQ2xKDf_complEquiv {n : ℕ} (p : Fin n) :
    Fin (n-1) ≃ {i : Fin n // i ≠ p} where
  toFun i :=
    ⟨⟨if (i:ℕ) < (p:ℕ) then (i:ℕ) else (i:ℕ)+1, by
        have hi := i.isLt; have hp := p.isLt
        split_ifs <;> omega⟩,
      by
        have hi := i.isLt; have hp := p.isLt
        intro h
        have hv : (if (i:ℕ) < (p:ℕ) then (i:ℕ) else (i:ℕ)+1) = (p:ℕ) :=
          congrArg Fin.val h
        split_ifs at hv <;> omega⟩
  invFun j :=
    ⟨if (j:ℕ) < (p:ℕ) then (j:ℕ) else (j:ℕ)-1, by
      have hj := j.1.isLt; have hp := p.isLt
      have hjne : (j:ℕ) ≠ (p:ℕ) := fun h => j.2 (Fin.ext h)
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
    have hjne : (j:ℕ) ≠ (p:ℕ) := fun h => j.2 (Fin.ext h)
    simp only [Fin.val_mk]
    split_ifs <;> omega

private lemma ggQ2xKDf_complEquiv_val {n : ℕ} (p : Fin n) (i : Fin (n-1)) :
    ((ggQ2xKDf_complEquiv p i : Fin n) : ℕ) =
      (if (i:ℕ) < (p:ℕ) then (i:ℕ) else (i:ℕ)+1) := rfl

private lemma ggQ2xKDf_D_shift {n : ℕ} (hn : 4 ≤ n) (i j : Fin (n-1)) :
    CartanMatrix.D n ⟨(i:ℕ)+1, by omega⟩ ⟨(j:ℕ)+1, by omega⟩ =
      CartanMatrix.D (n-1) i j := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.val_mk, Fin.mk.injEq, Fin.ext_iff,
    true_and, and_true]
  split_ifs <;> omega

private lemma ggQ2xKDf_D_zero_entry {n : ℕ} (hn : 4 ≤ n) (p : Fin n)
    (hp : (p:ℕ) = 0) (i j : Fin (n-1)) :
    CartanMatrix.D n (ggQ2xKDf_complEquiv p i) (ggQ2xKDf_complEquiv p j) =
      CartanMatrix.D (n-1) i j := by
  have h1 : ((ggQ2xKDf_complEquiv p i : Fin n)) =
      ⟨(i:ℕ)+1, by omega⟩ := by
    apply Fin.ext
    rw [ggQ2xKDf_complEquiv_val]
    simp [hp]
  have h2 : ((ggQ2xKDf_complEquiv p j : Fin n)) =
      ⟨(j:ℕ)+1, by omega⟩ := by
    apply Fin.ext
    rw [ggQ2xKDf_complEquiv_val]
    simp [hp]
  rw [h1, h2, ggQ2xKDf_D_shift hn]

private lemma ggQ2xKDf_D_fork {n : ℕ} (hn : 4 ≤ n) (p : Fin n)
    (hp : (p:ℕ) = n-2 ∨ (p:ℕ) = n-1) (i j : Fin (n-1)) :
    CartanMatrix.D n (ggQ2xKDf_complEquiv p i) (ggQ2xKDf_complEquiv p j) =
      CartanMatrix.A (n-1) i j := by
  rw [CartanMatrix.D, CartanMatrix.A]
  simp only [Matrix.of_apply, Fin.mk.injEq]
  by_cases hij : i = j
  · subst hij
    simp [ggQ2xKDf_complEquiv_val]
  · have hne : ¬ ((ggQ2xKDf_complEquiv p i : Fin n) =
        (ggQ2xKDf_complEquiv p j : Fin n)) := by
      intro hh
      exact hij ((ggQ2xKDf_complEquiv p).injective (Subtype.ext hh))
    simp only [if_neg hij, if_neg hne, ggQ2xKDf_complEquiv_val]
    split_ifs <;> omega

private lemma ggQ2xKDf_A_finCongr {m m' : ℕ} (h : m = m') (i j : Fin m) :
    CartanMatrix.A m' (finCongr h i) (finCongr h j) = CartanMatrix.A m i j := by
  subst h
  rfl

private lemma ggQ2xKDf_reindex {n m : ℕ} (p : Fin n)
    (M : Matrix (Fin m) (Fin m) (ZMod 3))
    (Cm : Matrix {i : Fin n // i ≠ p} {i : Fin n // i ≠ p} (ZMod 3))
    (e : Fin m ≃ {i : Fin n // i ≠ p})
    (hM : ∀ i j, M i j = Cm (e i) (e j))
    (κ : {i : Fin n // i ≠ p} → ZMod 3)
    (hκ : ∀ i, ∑ j, Cm i j * κ j = 0) :
    M.mulVec (fun i => κ (e i)) = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  calc ∑ j, M i j * κ (e j)
      = ∑ j, Cm (e i) (e j) * κ (e j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hM i j]
    _ = ∑ k, Cm (e i) k * κ k := Equiv.sum_comp e (fun k => Cm (e i) k * κ k)
    _ = 0 := hκ (e i)

private lemma ggQ2xKDf_kernel_zero_of_det {n m : ℕ} (p : Fin n)
    (M : Matrix (Fin m) (Fin m) (ZMod 3))
    (Cm : Matrix {i : Fin n // i ≠ p} {i : Fin n // i ≠ p} (ZMod 3))
    (e : Fin m ≃ {i : Fin n // i ≠ p})
    (hM : ∀ i j, M i j = Cm (e i) (e j))
    (κ : {i : Fin n // i ≠ p} → ZMod 3)
    (hκ : ∀ i, ∑ j, Cm i j * κ j = 0) (hdet : M.det ≠ 0) : κ = 0 := by
  have h0 := ggQ2xKDf_reindex p M Cm e hM κ hκ
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hdet h0
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  exact congrFun hz j

private lemma ggQ2xKDf_det_zero_of_ne {n m : ℕ} (p : Fin n)
    (M : Matrix (Fin m) (Fin m) (ZMod 3))
    (Cm : Matrix {i : Fin n // i ≠ p} {i : Fin n // i ≠ p} (ZMod 3))
    (e : Fin m ≃ {i : Fin n // i ≠ p})
    (hM : ∀ i j, M i j = Cm (e i) (e j))
    (κ : {i : Fin n // i ≠ p} → ZMod 3)
    (hκ : ∀ i, ∑ j, Cm i j * κ j = 0) (hκne : κ ≠ 0) : M.det = 0 := by
  by_contra hdet
  exact hκne (ggQ2xKDf_kernel_zero_of_det p M Cm e hM κ hκ hdet)

private lemma ggQ2xKDf_D_left {n : ℕ} (hn : 4 ≤ n) (i : Fin n)
    (h1 : 1 ≤ (i:ℕ)) (h2 : (i:ℕ) + 2 < n) :
    CartanMatrix.D n i ⟨(i:ℕ)-1, by omega⟩ = -1 := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.val_mk, Fin.mk.injEq, Fin.ext_iff,
    true_and, and_true]
  split_ifs <;> omega

private lemma ggQ2xKDf_D_right {n : ℕ} (hn : 4 ≤ n) (i : Fin n)
    (h : (i:ℕ) + 3 < n) :
    CartanMatrix.D n i ⟨(i:ℕ)+1, by omega⟩ = -1 := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.val_mk, Fin.mk.injEq, Fin.ext_iff,
    true_and, and_true]
  split_ifs <;> omega

private lemma ggQ2xKDf_D_fork_n2 {n : ℕ} (hn : 4 ≤ n) :
    CartanMatrix.D n ⟨n-3, by omega⟩ ⟨n-2, by omega⟩ = -1 := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.val_mk, Fin.mk.injEq, Fin.ext_iff,
    true_and, and_true]
  split_ifs <;> omega

private lemma ggQ2xKDf_leaf_D {n : ℕ} (hn : 4 ≤ n) (a₀ : Fin n)
    (h : ∃! c, c ≠ a₀ ∧ CartanMatrix.D n a₀ c ≠ 0) :
    (a₀:ℕ) = 0 ∨ (a₀:ℕ) = n-2 ∨ (a₀:ℕ) = n-1 := by
  obtain ⟨c, hc, huniq⟩ := h
  by_contra hnot
  push Not at hnot
  have hi0 : 1 ≤ (a₀:ℕ) := by omega
  have hi3 : (a₀:ℕ) ≤ n-3 := by omega
  have h2 : (a₀:ℕ) + 2 < n := by omega
  let c1 : Fin n := ⟨(a₀:ℕ)-1, by omega⟩
  have hc1ne : c1 ≠ a₀ := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [c1, Fin.val_mk] at hv
    omega
  have hc1D : CartanMatrix.D n a₀ c1 ≠ 0 := by
    have hd := ggQ2xKDf_D_left hn a₀ hi0 h2
    rw [hd]
    norm_num
  by_cases hlt : (a₀:ℕ) + 3 < n
  · let c2 : Fin n := ⟨(a₀:ℕ)+1, by omega⟩
    have hc2ne : c2 ≠ a₀ := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [c2, Fin.val_mk] at hv
      omega
    have hc2D : CartanMatrix.D n a₀ c2 ≠ 0 := by
      have hd := ggQ2xKDf_D_right hn a₀ hlt
      rw [hd]
      norm_num
    have hc12 : c1 ≠ c2 := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [c1, c2, Fin.val_mk] at hv
      omega
    exact hc12 ((huniq c1 ⟨hc1ne, hc1D⟩).trans (huniq c2 ⟨hc2ne, hc2D⟩).symm)
  · have hi_eq : (a₀:ℕ) = n-3 := by omega
    let c2 : Fin n := ⟨n-2, by omega⟩
    have hc2ne : c2 ≠ a₀ := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [c2, Fin.val_mk] at hv
      omega
    have hc2D : CartanMatrix.D n a₀ c2 ≠ 0 := by
      have hae : a₀ = (⟨n-3, by omega⟩ : Fin n) := Fin.ext hi_eq
      have hd := ggQ2xKDf_D_fork_n2 hn
      rw [hae]
      rw [show c2 = (⟨n-2, by omega⟩ : Fin n) from rfl]
      rw [hd]
      norm_num
    have hc12 : c1 ≠ c2 := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [c1, c2, Fin.val_mk] at hv
      omega
    exact hc12 ((huniq c1 ⟨hc1ne, hc1D⟩).trans (huniq c2 ⟨hc2ne, hc2D⟩).symm)

private lemma ggQ2xKDf_contra_D {n : ℕ} (hn : 4 ≤ n) (p : Fin n) (hp : (p:ℕ) = 0) :
    ¬ ∃ κ : {i : Fin n // i ≠ p} → ZMod 3, κ ≠ 0 ∧
      ∀ i : {i : Fin n // i ≠ p}, ∑ j : {j : Fin n // j ≠ p},
        ((CartanMatrix.D n i j : ℤ) : ZMod 3) * κ j = 0 := by
  rintro ⟨κ, hκne, hκ⟩
  let Cm : Matrix {i : Fin n // i ≠ p} {i : Fin n // i ≠ p} (ZMod 3) :=
    fun i j => ((CartanMatrix.D n i j : ℤ) : ZMod 3)
  have hκ' : ∀ i, ∑ j, Cm i j * κ j = 0 := hκ
  let e := ggQ2xKDf_complEquiv p
  let M : Matrix (Fin (n-1)) (Fin (n-1)) (ZMod 3) :=
    (CartanMatrix.D (n-1)).map (Int.castRingHom (ZMod 3))
  have hM : ∀ i j, M i j = Cm (e i) (e j) := by
    intro i j
    rw [show M i j = (((CartanMatrix.D (n-1)) i j : ℤ) : ZMod 3) from rfl,
      ← ggQ2xKDf_D_zero_entry hn p hp i j]
  have hdet : M.det ≠ 0 := by
    have h1 : M.det = (((CartanMatrix.D (n-1)).det : ℤ) : ZMod 3) :=
      (Int.cast_det (CartanMatrix.D (n-1))).symm
    rw [h1, CartanMatrix.D_det (by omega)]
    decide
  exact hκne (ggQ2xKDf_kernel_zero_of_det p M Cm e hM κ hκ' hdet)

private lemma ggQ2xKDf_fork_concl {n : ℕ} (hn : 4 ≤ n) (p : Fin n)
    (hp : (p:ℕ) = n-2 ∨ (p:ℕ) = n-1)
    (hker : ∃ κ : {i : Fin n // i ≠ p} → ZMod 3, κ ≠ 0 ∧
      ∀ i : {i : Fin n // i ≠ p}, ∑ j : {j : Fin n // j ≠ p},
        ((CartanMatrix.D n i j : ℤ) : ZMod 3) * κ j = 0) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ e : Fin (3 * k - 1) ≃ {i : Fin n // i ≠ p},
      ∀ i j, CartanMatrix.D n (e i) (e j) = CartanMatrix.A (3 * k - 1) i j := by
  obtain ⟨κ, hκne, hκ⟩ := hker
  let Cm : Matrix {i : Fin n // i ≠ p} {i : Fin n // i ≠ p} (ZMod 3) :=
    fun i j => ((CartanMatrix.D n i j : ℤ) : ZMod 3)
  have hκ' : ∀ i, ∑ j, Cm i j * κ j = 0 := hκ
  let e₀ := ggQ2xKDf_complEquiv p
  let M : Matrix (Fin (n-1)) (Fin (n-1)) (ZMod 3) :=
    (CartanMatrix.A (n-1)).map (Int.castRingHom (ZMod 3))
  have hM : ∀ i j, M i j = Cm (e₀ i) (e₀ j) := by
    intro i j
    rw [show M i j = (((CartanMatrix.A (n-1)) i j : ℤ) : ZMod 3) from rfl,
      ← ggQ2xKDf_D_fork hn p hp i j]
  have hdet0 : M.det = 0 :=
    ggQ2xKDf_det_zero_of_ne p M Cm e₀ hM κ hκ' hκne
  have h2 : (((CartanMatrix.A (n-1)).det : ℤ) : ZMod 3) = (n : ZMod 3) := by
    rw [CartanMatrix.A_det]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  have hnmod : (n : ZMod 3) = 0 := by
    have h1 : M.det = (((CartanMatrix.A (n-1)).det : ℤ) : ZMod 3) :=
      (Int.cast_det (CartanMatrix.A (n-1))).symm
    rw [← h2, ← h1, hdet0]
  have hdvd : 3 ∣ n := (ZMod.natCast_eq_zero_iff n 3).mp hnmod
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : 2 ≤ k := by omega
  have hEq : 3 * k - 1 = n - 1 := by omega
  refine ⟨k, hk2, (finCongr hEq).trans e₀, ?_⟩
  intro i j
  change CartanMatrix.D n (e₀ (finCongr hEq i)) (e₀ (finCongr hEq j)) =
    CartanMatrix.A (3 * k - 1) i j
  rw [ggQ2xKDf_D_fork hn p hp]
  exact ggQ2xKDf_A_finCongr hEq i j

theorem ggQ2xKD_class_D {n : ℕ} (hn : 4 ≤ n) (a₀ : Fin n)
    (h : ggQ2xKD_ClassHyp n (CartanMatrix.D n) a₀) :
    ggQ2xKD_ClassConcl n (CartanMatrix.D n) a₀ := by
  have hcases : (a₀:ℕ) = 0 ∨ (a₀:ℕ) = n-2 ∨ (a₀:ℕ) = n-1 :=
    ggQ2xKDf_leaf_D hn a₀ h.1
  rcases hcases with h0 | h2 | h1
  · exact (ggQ2xKDf_contra_D hn a₀ h0 h.2.2).elim
  · obtain ⟨k, hk2, e, he⟩ := ggQ2xKDf_fork_concl hn a₀ (Or.inl h2) h.2.2
    exact Or.inl ⟨k, hk2, e, he⟩
  · obtain ⟨k, hk2, e, he⟩ := ggQ2xKDf_fork_concl hn a₀ (Or.inr h1) h.2.2
    exact Or.inl ⟨k, hk2, e, he⟩
end CFSG.StandardType

end

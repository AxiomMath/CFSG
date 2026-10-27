module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggQ2s08d4_R_symm {ι : Type} (M : CoxeterMatrix ι) :
    Symmetric (fun a b : ι => a ≠ b ∧ M a b ≠ 2) := by
  intro a b hab
  exact ⟨hab.1.symm, by rw [CoxeterMatrix.symmetric M b a]; exact hab.2⟩

private theorem ggQ2s08d4_conn_of_spine {α : Type} (R : α → α → Prop) (hsym : Symmetric R)
    (z : α) (h : ∀ k, Relation.ReflTransGen R z k) :
    ∀ i j, Relation.ReflTransGen R i j := by
  have hrev : ∀ {a b : α}, Relation.ReflTransGen R a b → Relation.ReflTransGen R b a := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (hsym hbc) ih
  intro i j
  exact (hrev (h i)).trans (h j)

private theorem ggQ2s08d4_conn_reindex {n : ℕ} {X : CoxeterMatrix (Fin n)} {ι : Type}
    (e : Fin n ≃ ι)
    (hX : ∀ i j : Fin n,
      Relation.ReflTransGen (fun a b : Fin n => a ≠ b ∧ X a b ≠ 2) i j) :
    ∀ i j : ι,
      Relation.ReflTransGen (fun a b : ι => a ≠ b ∧ (X.reindex e) a b ≠ 2) i j := by
  intro i j
  have hconn : ∀ x y : Fin n,
      (fun a b : Fin n => a ≠ b ∧ X a b ≠ 2) x y →
      (fun a b : ι => a ≠ b ∧ (X.reindex e) a b ≠ 2) (e x) (e y) := by
    intro x y hxy
    refine ⟨?_, ?_⟩
    · exact fun h => hxy.1 (e.injective h)
    · intro h6
      exact hxy.2 (by simpa [CoxeterMatrix.reindex_apply] using h6)
  have h := Relation.ReflTransGen.lift (f := e)
    (p := fun a b : ι => a ≠ b ∧ (X.reindex e) a b ≠ 2) hconn
    (e.symm i) (e.symm j) (hX (e.symm i) (e.symm j))
  have h2 : Relation.ReflTransGen (fun a b : ι => a ≠ b ∧ (X.reindex e) a b ≠ 2)
      (e (e.symm i)) (e (e.symm j)) := h
  simpa using h2

private theorem ggQ2s08d4_ne_six_reindex {n : ℕ} {X : CoxeterMatrix (Fin n)} {ι : Type}
    (hX : ∀ i j : Fin n, X i j ≠ 6) (e : Fin n ≃ ι) :
    ∀ i j : ι, i ≠ j → (X.reindex e) i j ≠ 6 := by
  intro i j _ h
  exact hX (e.symm i) (e.symm j) (by simpa [CoxeterMatrix.reindex_apply] using h)

private theorem ggQ2s08d4_A_ne_six (n : ℕ) (i j : Fin n) : CoxeterMatrix.A n i j ≠ 6 := by
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  split_ifs <;> omega

private theorem ggQ2s08d4_B_ne_six (n : ℕ) (i j : Fin n) : CoxeterMatrix.B n i j ≠ 6 := by
  simp only [CoxeterMatrix.B, Matrix.of_apply]
  split_ifs <;> omega

private theorem ggQ2s08d4_D_ne_six (n : ℕ) (i j : Fin n) : ggCoxeterMatrixD n i j ≠ 6 := by
  rw [ggCoxeterMatrixD_apply]
  split_ifs <;> omega

private theorem ggQ2s08d4_A_step (n m : ℕ) (hmn : m < n) (hm : m + 1 < n) :
    (fun a b : Fin n => a ≠ b ∧ CoxeterMatrix.A n a b ≠ 2)
      ⟨m, hmn⟩ ⟨m + 1, hm⟩ := by
  refine ⟨?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  · simp only [CoxeterMatrix.A, Matrix.of_apply]
    rw [if_neg (by intro h; have hv := congrArg Fin.val h; simp only [Fin.val_mk] at hv; omega)]
    split_ifs <;> simp_all

private theorem ggQ2s08d4_B_step (n m : ℕ) (hmn : m < n) (hm : m + 1 < n) :
    (fun a b : Fin n => a ≠ b ∧ CoxeterMatrix.B n a b ≠ 2)
      ⟨m, hmn⟩ ⟨m + 1, hm⟩ := by
  refine ⟨?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  · simp only [CoxeterMatrix.B, Matrix.of_apply]
    rw [if_neg (by intro h; have hv := congrArg Fin.val h; simp only [Fin.val_mk] at hv; omega)]
    split_ifs <;> simp_all

private theorem ggQ2s08d4_conn_A (n : ℕ) (hn : 1 ≤ n) :
    ∀ i j : Fin n,
      Relation.ReflTransGen (fun a b : Fin n => a ≠ b ∧ CoxeterMatrix.A n a b ≠ 2) i j := by
  apply ggQ2s08d4_conn_of_spine _ (ggQ2s08d4_R_symm _) ⟨0, hn⟩
  intro k
  have key : ∀ m (hm : m < n),
      Relation.ReflTransGen (fun a b : Fin n => a ≠ b ∧ CoxeterMatrix.A n a b ≠ 2)
        ⟨0, hn⟩ ⟨m, hm⟩ := by
    intro m
    induction m with
    | zero => intro hm; exact Relation.ReflTransGen.refl
    | succ m ih =>
        intro hm
        have hmn : m < n := by omega
        exact Relation.ReflTransGen.tail (ih hmn) (ggQ2s08d4_A_step n m hmn hm)
  simpa using key k.val k.is_lt

private theorem ggQ2s08d4_conn_B (n : ℕ) (hn : 1 ≤ n) :
    ∀ i j : Fin n,
      Relation.ReflTransGen (fun a b : Fin n => a ≠ b ∧ CoxeterMatrix.B n a b ≠ 2) i j := by
  apply ggQ2s08d4_conn_of_spine _ (ggQ2s08d4_R_symm _) ⟨0, hn⟩
  intro k
  have key : ∀ m (hm : m < n),
      Relation.ReflTransGen (fun a b : Fin n => a ≠ b ∧ CoxeterMatrix.B n a b ≠ 2)
        ⟨0, hn⟩ ⟨m, hm⟩ := by
    intro m
    induction m with
    | zero => intro hm; exact Relation.ReflTransGen.refl
    | succ m ih =>
        intro hm
        have hmn : m < n := by omega
        exact Relation.ReflTransGen.tail (ih hmn) (ggQ2s08d4_B_step n m hmn hm)
  simpa using key k.val k.is_lt

private theorem ggQ2s08d4_D_chain (n m : ℕ) (hn : 3 ≤ n) (hmn : m < n) (hm : m + 1 < n)
    (h3 : m + 3 < n) :
    (fun a b : Fin n => a ≠ b ∧ ggCoxeterMatrixD n a b ≠ 2)
      ⟨m, hmn⟩ ⟨m + 1, hm⟩ := by
  have hne : (⟨m, hmn⟩ : Fin n) ≠ ⟨m + 1, hm⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  refine ⟨hne, ?_⟩
  rw [ggCoxeterMatrixD_apply]
  rw [if_neg hne]
  have hcart : CartanMatrix.D n ⟨m, hmn⟩ ⟨m + 1, hm⟩ = -1 := by
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.val_mk, Fin.ext_iff, true_and]
    split_ifs <;> omega
  rw [if_neg (by rw [hcart]; norm_num)]
  norm_num

private theorem ggQ2s08d4_D_fork2 (n : ℕ) (hn : 3 ≤ n) :
    (fun a b : Fin n => a ≠ b ∧ ggCoxeterMatrixD n a b ≠ 2)
      ⟨n - 3, by omega⟩ ⟨n - 2, by omega⟩ := by
  have hne : (⟨n - 3, by omega⟩ : Fin n) ≠ ⟨n - 2, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  refine ⟨hne, ?_⟩
  rw [ggCoxeterMatrixD_apply]
  rw [if_neg hne]
  have hcart : CartanMatrix.D n ⟨n - 3, by omega⟩ ⟨n - 2, by omega⟩ = -1 := by
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.val_mk, Fin.ext_iff, true_and]
    split_ifs <;> omega
  rw [if_neg (by rw [hcart]; norm_num)]
  norm_num

private theorem ggQ2s08d4_D_fork1 (n : ℕ) (hn : 3 ≤ n) :
    (fun a b : Fin n => a ≠ b ∧ ggCoxeterMatrixD n a b ≠ 2)
      ⟨n - 3, by omega⟩ ⟨n - 1, by omega⟩ := by
  have hne : (⟨n - 3, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  refine ⟨hne, ?_⟩
  rw [ggCoxeterMatrixD_apply]
  rw [if_neg hne]
  have hcart : CartanMatrix.D n ⟨n - 3, by omega⟩ ⟨n - 1, by omega⟩ = -1 := by
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.val_mk, Fin.ext_iff, true_and]
    split_ifs <;> omega
  rw [if_neg (by rw [hcart]; norm_num)]
  norm_num

private theorem ggQ2s08d4_conn_D (n : ℕ) (hn : 3 ≤ n) :
    ∀ i j : Fin n,
      Relation.ReflTransGen (fun a b : Fin n => a ≠ b ∧ ggCoxeterMatrixD n a b ≠ 2) i j := by
  apply ggQ2s08d4_conn_of_spine _ (ggQ2s08d4_R_symm _) ⟨0, by omega⟩
  intro k
  have key : ∀ m (hm : m < n), m ≤ n - 2 →
      Relation.ReflTransGen (fun a b : Fin n => a ≠ b ∧ ggCoxeterMatrixD n a b ≠ 2)
        ⟨0, by omega⟩ ⟨m, hm⟩ := by
    intro m
    induction m with
    | zero => intro hm _; exact Relation.ReflTransGen.refl
    | succ m ih =>
        intro hm hle
        have hmn : m < n := by omega
        have hmle : m ≤ n - 2 := by omega
        refine Relation.ReflTransGen.tail (ih hmn hmle) ?_
        by_cases hchain : m + 3 < n
        · exact ggQ2s08d4_D_chain n m hn hmn hm hchain
        · have hm3 : m = n - 3 := by omega
          subst hm3
          have hval : n - 3 + 1 = n - 2 := by omega
          simpa [hval] using ggQ2s08d4_D_fork2 n hn
  by_cases hk : (k : ℕ) ≤ n - 2
  · simpa using key k.val k.is_lt hk
  · have hk1 : (k : ℕ) = n - 1 := by omega
    have h03 : Relation.ReflTransGen
        (fun a b : Fin n => a ≠ b ∧ ggCoxeterMatrixD n a b ≠ 2)
        ⟨0, by omega⟩ ⟨n - 3, by omega⟩ := by
      simpa using key (n - 3) (by omega) (by omega)
    have hstep := ggQ2s08d4_D_fork1 n hn
    have hlt : Relation.ReflTransGen
        (fun a b : Fin n => a ≠ b ∧ ggCoxeterMatrixD n a b ≠ 2)
        ⟨0, by omega⟩ ⟨n - 1, by omega⟩ := Relation.ReflTransGen.tail h03 hstep
    have hkfin : k = ⟨n - 1, by omega⟩ := Fin.ext hk1
    rw [hkfin]
    exact hlt

theorem ggQ2s08d_label_connected {lab : LargeEvenLabel} (hlab : GGQ2S08BigLabel lab)
    {ι : Type} (M : CoxeterMatrix ι) (hMW : GGQ2LabelWeyl lab M) :
    (∀ i j : ι, Relation.ReflTransGen (fun a b => a ≠ b ∧ M a b ≠ 2) i j) ∧
      (∀ i j : ι, i ≠ j → M i j ≠ 6) := by
  obtain ⟨hq, htag, hrank⟩ := hlab
  rcases htag with hA | hB | hC | hD | hD
  · simp only [GGQ2LabelWeyl, hA] at hMW
    rcases hMW with ⟨e, rfl⟩
    exact ⟨ggQ2s08d4_conn_reindex e (ggQ2s08d4_conn_A lab.rank (by omega)),
      ggQ2s08d4_ne_six_reindex (ggQ2s08d4_A_ne_six lab.rank) e⟩
  · simp only [GGQ2LabelWeyl, hB] at hMW
    rcases hMW with ⟨e, rfl⟩
    exact ⟨ggQ2s08d4_conn_reindex e (ggQ2s08d4_conn_B lab.rank (by omega)),
      ggQ2s08d4_ne_six_reindex (ggQ2s08d4_B_ne_six lab.rank) e⟩
  · simp only [GGQ2LabelWeyl, hC] at hMW
    rcases hMW with ⟨e, rfl⟩
    exact ⟨ggQ2s08d4_conn_reindex e (ggQ2s08d4_conn_B lab.rank (by omega)),
      ggQ2s08d4_ne_six_reindex (ggQ2s08d4_B_ne_six lab.rank) e⟩
  · simp only [GGQ2LabelWeyl, hD] at hMW
    rcases hMW with ⟨e, rfl⟩
    exact ⟨ggQ2s08d4_conn_reindex e (ggQ2s08d4_conn_D lab.rank (by omega)),
      ggQ2s08d4_ne_six_reindex (ggQ2s08d4_D_ne_six lab.rank) e⟩
  · simp only [GGQ2LabelWeyl, hD] at hMW
    rcases hMW with ⟨e, rfl⟩
    exact ⟨ggQ2s08d4_conn_reindex e (ggQ2s08d4_conn_D lab.rank (by omega)),
      ggQ2s08d4_ne_six_reindex (ggQ2s08d4_D_ne_six lab.rank) e⟩

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGHalfSlOn
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockTorus
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockPerm

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

private abbrev MatN (m : ℕ) := Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2

private def Sset (m : ℕ) : Set (Fin (m + 1 + 1 + 1)) := {j | 2 ≤ j.val ∧ j.val ≤ m}

private theorem f2_eq_zero_or_one (z : F2) : z = 0 ∨ z = 1 := by
  have hcard : Nat.card F2 = 2 := by
    have := GaloisField.card 2 1 (by omega)
    simpa using this
  by_cases hz : z = 0
  · exact Or.inl hz
  · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
    exact Or.inr ((huniq z hz).trans (huniq 1 one_ne_zero).symm)

private theorem mul_inv_mul_mul_self {G : Type*} [Group G] {x y : G} (hx : x * x = 1) :
    (x * y * x) * x = x * y := by
  rw [mul_assoc (x * y) x x, hx, mul_one]

private theorem omegaBlock_eq_mul (n : ℕ) (k : Fin n) :
    omegaBlock n k =
      SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne
          (1 : F2) *
        SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne.symm 1 := by
  have hx2 : SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : F2) *
      SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 = 1 := by
    have hneg : (-1 : F2) = 1 := by
      rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]
    have ht := Matrix.SpecialLinearGroup.transvection_mul_neg
      (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : F2)
    rwa [hneg] at ht
  have hneg : (-1 : F2) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]
  rw [omegaBlock, weylRep, hneg]
  exact mul_inv_mul_mul_self hx2

private theorem coe_omegaBlock_sum (n : ℕ) (k : Fin n) :
    ((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      1 + Matrix.single k.castSucc k.succ (1 : F2) +
        Matrix.single k.succ k.castSucc 1 + Matrix.single k.castSucc k.castSucc 1 := by
  rw [omegaBlock_eq_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
  rw [Matrix.single_mul_single_same, one_mul]
  abel

private theorem sq_formula {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    (1 + Matrix.single i j (1 : F2) + Matrix.single j i 1 + Matrix.single i i 1) *
        (1 + Matrix.single i j 1 + Matrix.single j i 1 + Matrix.single i i 1) =
      1 + Matrix.single i j 1 + Matrix.single j i 1 + Matrix.single j j 1 := by
  have hAA : Matrix.single i j (1 : F2) * Matrix.single i j 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne]
    exact hij.symm
  have hAB : Matrix.single i j (1 : F2) * Matrix.single j i 1 = Matrix.single i i 1 := by
    rw [Matrix.single_mul_single_same, mul_one]
  have hAC : Matrix.single i j (1 : F2) * Matrix.single i i 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne]
    exact hij.symm
  have hBA : Matrix.single j i (1 : F2) * Matrix.single i j 1 = Matrix.single j j 1 := by
    rw [Matrix.single_mul_single_same, mul_one]
  have hBB : Matrix.single j i (1 : F2) * Matrix.single j i 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne]
    exact hij
  have hBC : Matrix.single j i (1 : F2) * Matrix.single i i 1 = Matrix.single j i 1 := by
    rw [Matrix.single_mul_single_same, mul_one]
  have hCA : Matrix.single i i (1 : F2) * Matrix.single i j 1 = Matrix.single i j 1 := by
    rw [Matrix.single_mul_single_same, mul_one]
  have hCB : Matrix.single i i (1 : F2) * Matrix.single j i 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne]
    exact hij
  have hCC : Matrix.single i i (1 : F2) * Matrix.single i i 1 = Matrix.single i i 1 := by
    rw [Matrix.single_mul_single_same, mul_one]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [hAA, hAB, hAC, hBA, hBB, hBC, hCA, hCB, hCC]
  ext r c
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all [gf2_two, one_add_one_eq_two]

private theorem coe_omegaBlock_sq_sum (n : ℕ) (k : Fin n) :
    (((omegaBlock n k) ^ 2 : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      1 + Matrix.single k.castSucc k.succ (1 : F2) +
        Matrix.single k.succ k.castSucc 1 + Matrix.single k.succ k.succ 1 := by
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_omegaBlock_sum]
  exact sq_formula (show k.castSucc ≠ k.succ from Fin.castSucc_lt_succ.ne)

private theorem mul_single_apply' {N : ℕ} (M : Matrix (Fin N) (Fin N) F2) (i j : Fin N)
    (c0 : F2) (r c : Fin N) :
    (M * Matrix.single i j c0) r c = if c = j then M r i * c0 else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · by_cases hcj : c = j
    · rw [hcj, Matrix.single_apply_same, if_pos rfl]
    · rw [if_neg hcj, Matrix.single_apply,
        if_neg (by rintro ⟨-, h⟩; exact hcj h.symm), mul_zero]
  · intro x _ hx
    rw [Matrix.single_apply, if_neg (by rintro ⟨h, -⟩; exact hx h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem single_mul_apply' {N : ℕ} (M : Matrix (Fin N) (Fin N) F2) (i j : Fin N)
    (c0 : F2) (r c : Fin N) :
    (Matrix.single i j c0 * M) r c = if r = i then c0 * M j c else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · by_cases hri : r = i
    · rw [hri, Matrix.single_apply_same, if_pos rfl]
    · rw [if_neg hri, Matrix.single_apply,
        if_neg (by rintro ⟨h, -⟩; exact hri h.symm), zero_mul]
  · intro x _ hx
    rw [Matrix.single_apply, if_neg (by rintro ⟨-, h⟩; exact hx h.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem commute_single_of_commute_slOn {N : ℕ} {S : Set (Fin N)}
    {d : SpecialLinearGroup (Fin N) F2}
    (hS : ∀ s ∈ slOn N S, d * s = s * d)
    {a b : Fin N} (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S) :
    Commute (Matrix.single a b (1 : F2)) (d : Matrix (Fin N) (Fin N) F2) := by
  have ht : SpecialLinearGroup.transvection hab (1 : F2) ∈ slOn N S :=
    transvection_mem_slOn hab 1 ha hb
  have h := congrArg (fun x : SpecialLinearGroup (Fin N) F2 =>
      (x : Matrix (Fin N) (Fin N) F2)) (hS _ ht)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe] at h
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at h
  exact (add_left_cancel h).symm

private theorem exists_ne_mem_S {m : ℕ} (hm : 3 ≤ m) {a : Fin (m + 1 + 1 + 1)}
    (ha : a ∈ Sset m) : ∃ b ∈ Sset m, b ≠ a := by
  by_cases h2 : a = ⟨2, by omega⟩
  · refine ⟨⟨3, by omega⟩, ?_, ?_⟩
    · simp only [Sset, Set.mem_setOf_eq]; omega
    · rw [h2]
      intro h
      exact absurd (Fin.ext_iff.mp h) (by norm_num)
  · refine ⟨⟨2, by omega⟩, ?_, ?_⟩
    · simp only [Sset, Set.mem_setOf_eq]; omega
    · exact fun h => h2 h.symm

private theorem col_row_of_commute_slOn {m : ℕ} (hm : 3 ≤ m)
    {d : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (hS : ∀ s ∈ slOn (m + 1 + 1 + 1) (Sset m), d * s = s * d)
    {a : Fin (m + 1 + 1 + 1)} (ha : a ∈ Sset m) :
    (∀ r, r ≠ a → (d : MatN m) r a = 0) ∧
    (∀ r, r ≠ a → (d : MatN m) a r = 0) := by
  obtain ⟨b, hb, hba⟩ := exists_ne_mem_S hm ha
  have hab : a ≠ b := hba.symm
  have hc : Commute (Matrix.single a b 1) (d : MatN m) :=
    commute_single_of_commute_slOn hS hab ha hb
  have hc' : Commute (Matrix.single b a 1) (d : MatN m) :=
    commute_single_of_commute_slOn hS hba hb ha
  exact ⟨fun r hr => Matrix.col_eq_zero_of_commute_single hc hr,
    fun r hr => Matrix.row_eq_zero_of_commute_single hc' hr⟩

private theorem diag_eq_one_of_commute_slOn {m : ℕ} (hm : 3 ≤ m)
    {d : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (hS : ∀ s ∈ slOn (m + 1 + 1 + 1) (Sset m), d * s = s * d)
    {a : Fin (m + 1 + 1 + 1)} (ha : a ∈ Sset m) :
    (d : MatN m) a a = 1 := by
  have hrow : ∀ r, r ≠ a → (d : MatN m) a r = 0 := (col_row_of_commute_slOn hm hS ha).2
  have hprod : ((d : MatN m) * ((d⁻¹ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m)) = 1 := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 => (x : MatN m))
      (mul_inv_cancel d)
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
  have hkey : (d : MatN m) a a *
      ((d⁻¹ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m) a a = 1 := by
    have h := congrFun (congrFun hprod a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a, Matrix.one_apply_eq] at h
    · exact h
    · intro x _ hx
      rw [hrow x hx, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  have hne : (d : MatN m) a a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hkey
    exact zero_ne_one hkey
  rcases f2_eq_zero_or_one _ with h | h
  · exact absurd h hne
  · exact h

private theorem omega_comm_entries {N : ℕ} {X : Matrix (Fin N) (Fin N) F2} {i j : Fin N}
    (hij : i ≠ j)
    (h : X * (1 + Matrix.single i j 1 + Matrix.single j i 1 + Matrix.single i i 1) =
         (1 + Matrix.single i j 1 + Matrix.single j i 1 + Matrix.single i i 1) * X) :
    (∀ r, r ≠ i → r ≠ j → X r i = 0 ∧ X r j = 0) ∧
    (∀ c, c ≠ i → c ≠ j → X i c = 0 ∧ X j c = 0) ∧
    X j i = X i j ∧ X j j = X i i + X i j := by
  have hrc : ∀ r c, (if c = j then X r i else 0) + (if c = i then X r j else 0) +
        (if c = i then X r i else 0) =
      (if r = i then X j c else 0) + (if r = j then X i c else 0) +
        (if r = i then X i c else 0) := by
    intro r c
    have hX := h
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hX
    have h' := congrFun (congrFun hX r) c
    simp only [Matrix.add_apply, mul_single_apply', single_mul_apply', mul_one, one_mul] at h'
    simpa only [add_assoc] using add_left_cancel (by simpa only [add_assoc] using h')
  have hri : ∀ r, r ≠ i → r ≠ j → X r i = 0 := by
    intro r hr_i hr_j
    have h := hrc r j
    simp only [if_pos rfl, if_neg hij.symm, if_neg hr_i, if_neg hr_j, if_true, if_false,
      add_zero, zero_add] at h
    exact h
  have hrj : ∀ r, r ≠ i → r ≠ j → X r j = 0 := by
    intro r hr_i hr_j
    have h := hrc r i
    simp only [if_neg hij, if_pos rfl, if_neg hr_i, if_neg hr_j, if_true, if_false,
      add_zero, zero_add] at h
    rw [hri r hr_i hr_j, add_zero] at h
    exact h
  have hic : ∀ c, c ≠ i → c ≠ j → X i c = 0 := by
    intro c hc_i hc_j
    have h := hrc j c
    simp only [if_neg hc_j, if_neg hc_i, if_neg hij.symm, if_pos rfl, if_true, if_false,
      add_zero, zero_add] at h
    exact h.symm
  have hjc : ∀ c, c ≠ i → c ≠ j → X j c = 0 := by
    intro c hc_i hc_j
    have h := hrc i c
    simp only [if_neg hc_j, if_neg hc_i, if_pos rfl, if_neg hij, if_true, if_false,
      add_zero, zero_add] at h
    rw [hic c hc_i hc_j, add_zero] at h
    exact h.symm
  have hji : X j i = X i j := by
    have h := hrc j j
    simp only [if_pos rfl, if_neg hij.symm, if_true, if_false, add_zero, zero_add] at h
    exact h
  have hjj : X j j = X i i + X i j := by
    have h := hrc i j
    simp only [if_pos rfl, if_neg hij.symm, if_neg hij, if_true, if_false, add_zero,
      zero_add] at h
    have h2 : X i j + X i j = (0 : F2) := by
      linear_combination (X i j) * gf2_two
    calc X j j = X j j + (X i j + X i j) := by rw [h2, add_zero]
      _ = (X j j + X i j) + X i j := (add_assoc _ _ _).symm
      _ = X i i + X i j := by rw [← h]
  exact ⟨fun r hr_i hr_j => ⟨hri r hr_i hr_j, hrj r hr_i hr_j⟩,
    fun c hc_i hc_j => ⟨hic c hc_i hc_j, hjc c hc_i hc_j⟩, hji, hjj⟩

private def z0 (m : ℕ) : Fin (m + 1 + 1 + 1) := (⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc

private def o1 (m : ℕ) : Fin (m + 1 + 1 + 1) := (⟨0, by omega⟩ : Fin (m + 1 + 1)).succ

private def zk (m : ℕ) : Fin (m + 1 + 1 + 1) := (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc

private def ok (m : ℕ) : Fin (m + 1 + 1 + 1) := (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ

private theorem z0_val (m : ℕ) : (z0 m).val = 0 := rfl
private theorem o1_val (m : ℕ) : (o1 m).val = 1 := rfl
private theorem zk_val (m : ℕ) : (zk m).val = m + 1 := rfl
private theorem ok_val (m : ℕ) : (ok m).val = m + 2 := rfl

private theorem z0_ne_o1 (m : ℕ) : z0 m ≠ o1 m := by
  intro h; have := congrArg Fin.val h; simp [z0_val, o1_val] at this

private theorem z0_not_mem_S (m : ℕ) : z0 m ∉ Sset m := by
  simp only [Sset, Set.mem_setOf_eq, z0_val]; omega

private theorem o1_not_mem_S (m : ℕ) : o1 m ∉ Sset m := by
  simp only [Sset, Set.mem_setOf_eq, o1_val]; omega

private theorem zk_not_mem_S (m : ℕ) : zk m ∉ Sset m := by
  simp only [Sset, Set.mem_setOf_eq, zk_val]; omega

private theorem ok_not_mem_S (m : ℕ) : ok m ∉ Sset m := by
  simp only [Sset, Set.mem_setOf_eq, ok_val]; omega

private theorem z0_ne_zk (m : ℕ) (hm : 3 ≤ m) : z0 m ≠ zk m := by
  intro h
  have h1 := congrArg Fin.val h
  rw [z0_val, zk_val] at h1
  omega

private theorem z0_ne_ok (m : ℕ) (hm : 3 ≤ m) : z0 m ≠ ok m := by
  intro h
  have h1 := congrArg Fin.val h
  rw [z0_val, ok_val] at h1
  omega

private theorem o1_ne_zk (m : ℕ) (hm : 3 ≤ m) : o1 m ≠ zk m := by
  intro h
  have h1 := congrArg Fin.val h
  rw [o1_val, zk_val] at h1
  omega

private theorem o1_ne_ok (m : ℕ) (hm : 3 ≤ m) : o1 m ≠ ok m := by
  intro h
  have h1 := congrArg Fin.val h
  rw [o1_val, ok_val] at h1
  omega

private theorem zk_ne_ok (m : ℕ) : zk m ≠ ok m := by
  intro h; have := congrArg Fin.val h; simp [zk_val, ok_val] at this

private theorem eq_special_of_not_mem_S {m : ℕ} (hm : 3 ≤ m) {x : Fin (m + 1 + 1 + 1)}
    (hx : x ∉ Sset m) : x = z0 m ∨ x = o1 m ∨ x = zk m ∨ x = ok m := by
  have hxlt : x.val < m + 3 := x.isLt
  have h : x.val = 0 ∨ x.val = 1 ∨ x.val = m + 1 ∨ x.val = m + 2 := by
    simp only [Sset, Set.mem_setOf_eq, not_and, not_le] at hx
    omega
  rcases h with h | h | h | h
  · left; apply Fin.ext; simp [z0_val, h]
  · right; left; apply Fin.ext; simp [o1_val, h]
  · right; right; left; apply Fin.ext; simp [zk_val, h]
  · right; right; right; apply Fin.ext; simp [ok_val, h]

private def ShapeFacts {m : ℕ} (X : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : Prop :=
  (∀ a ∈ Sset m, (X : MatN m) a a = 1) ∧
  (∀ a ∈ Sset m, ∀ r, r ≠ a → (X : MatN m) r a = 0 ∧ (X : MatN m) a r = 0) ∧
  (∀ r, r ≠ z0 m → r ≠ o1 m → (X : MatN m) r (z0 m) = 0 ∧ (X : MatN m) r (o1 m) = 0) ∧
  (∀ c, c ≠ z0 m → c ≠ o1 m → (X : MatN m) (z0 m) c = 0 ∧ (X : MatN m) (o1 m) c = 0) ∧
  ((X : MatN m) (o1 m) (z0 m) = (X : MatN m) (z0 m) (o1 m) ∧
    (X : MatN m) (o1 m) (o1 m) = (X : MatN m) (z0 m) (z0 m) + (X : MatN m) (z0 m) (o1 m)) ∧
  (∀ r, r ≠ zk m → r ≠ ok m → (X : MatN m) r (zk m) = 0 ∧ (X : MatN m) r (ok m) = 0) ∧
  (∀ c, c ≠ zk m → c ≠ ok m → (X : MatN m) (zk m) c = 0 ∧ (X : MatN m) (ok m) c = 0) ∧
  ((X : MatN m) (ok m) (zk m) = (X : MatN m) (zk m) (ok m) ∧
    (X : MatN m) (ok m) (ok m) = (X : MatN m) (zk m) (zk m) + (X : MatN m) (zk m) (ok m))

private theorem shape_facts {m : ℕ} (hm : 3 ≤ m)
    {X : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (hS : ∀ s ∈ slOn (m + 1 + 1 + 1) (Sset m), X * s = s * X)
    (h0 : X * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ =
      omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * X)
    (hk : X * omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ =
      omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ * X) :
    ShapeFacts X := by
  have hdiag : ∀ a ∈ Sset m, (X : MatN m) a a = 1 :=
    fun a ha => diag_eq_one_of_commute_slOn hm hS ha
  have hcr : ∀ a ∈ Sset m, ∀ r, r ≠ a → (X : MatN m) r a = 0 ∧ (X : MatN m) a r = 0 :=
    fun a ha r hr => ⟨(col_row_of_commute_slOn hm hS ha).1 r hr,
      (col_row_of_commute_slOn hm hS ha).2 r hr⟩
  have h0m : (X : MatN m) * (1 + Matrix.single (z0 m) (o1 m) 1 + Matrix.single (o1 m) (z0 m) 1 +
      Matrix.single (z0 m) (z0 m) 1) =
      (1 + Matrix.single (z0 m) (o1 m) 1 + Matrix.single (o1 m) (z0 m) 1 +
        Matrix.single (z0 m) (z0 m) 1) * (X : MatN m) := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 => (x : MatN m)) h0
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
    have hcoe := coe_omegaBlock_sum (m + 1 + 1) (⟨0, by omega⟩ : Fin (m + 1 + 1))
    rw [hcoe] at h
    simpa only [z0, o1] using h
  have hkm : (X : MatN m) * (1 + Matrix.single (zk m) (ok m) 1 + Matrix.single (ok m) (zk m) 1 +
      Matrix.single (zk m) (zk m) 1) =
      (1 + Matrix.single (zk m) (ok m) 1 + Matrix.single (ok m) (zk m) 1 +
        Matrix.single (zk m) (zk m) 1) * (X : MatN m) := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 => (x : MatN m)) hk
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
    have hcoe := coe_omegaBlock_sum (m + 1 + 1) (⟨m + 1, by omega⟩ : Fin (m + 1 + 1))
    rw [hcoe] at h
    simpa only [zk, ok] using h
  have h0e := omega_comm_entries (z0_ne_o1 m) h0m
  have hke := omega_comm_entries (zk_ne_ok m) hkm
  exact ⟨hdiag, hcr, h0e.1, h0e.2.1, h0e.2.2, hke.1, hke.2.1, hke.2.2⟩

private theorem eq_of_params {m : ℕ} (hm : 3 ≤ m)
    {X Y : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (hX : ShapeFacts X) (hY : ShapeFacts Y)
    (hii : (X : MatN m) (z0 m) (z0 m) = (Y : MatN m) (z0 m) (z0 m))
    (hij : (X : MatN m) (z0 m) (o1 m) = (Y : MatN m) (z0 m) (o1 m))
    (hki : (X : MatN m) (zk m) (zk m) = (Y : MatN m) (zk m) (zk m))
    (hkj : (X : MatN m) (zk m) (ok m) = (Y : MatN m) (zk m) (ok m)) :
    X = Y := by
  apply Subtype.ext
  apply Matrix.ext
  intro r c
  obtain ⟨hXd, hXcr, hX0r, hX0c, hX0b, hXKr, hXKc, hXKb⟩ := hX
  obtain ⟨hYd, hYcr, hY0r, hY0c, hY0b, hYKr, hYKc, hYKb⟩ := hY
  by_cases hrS : r ∈ Sset m
  · by_cases hcS : c ∈ Sset m
    · by_cases hrc : r = c
      · subst hrc; rw [hXd r hrS, hYd r hrS]
      · have hcr : c ≠ r := fun h => hrc h.symm
        rw [(hXcr r hrS c hcr).2, (hYcr r hrS c hcr).2]
    · rcases eq_special_of_not_mem_S hm hcS with hc | hc | hc | hc
      · subst hc
        rw [(hX0r r (fun h => z0_not_mem_S m (h ▸ hrS)) (fun h => o1_not_mem_S m (h ▸ hrS))).1,
          (hY0r r (fun h => z0_not_mem_S m (h ▸ hrS)) (fun h => o1_not_mem_S m (h ▸ hrS))).1]
      · subst hc
        rw [(hX0r r (fun h => z0_not_mem_S m (h ▸ hrS)) (fun h => o1_not_mem_S m (h ▸ hrS))).2,
          (hY0r r (fun h => z0_not_mem_S m (h ▸ hrS)) (fun h => o1_not_mem_S m (h ▸ hrS))).2]
      · subst hc
        rw [(hXKr r (fun h => zk_not_mem_S m (h ▸ hrS)) (fun h => ok_not_mem_S m (h ▸ hrS))).1,
          (hYKr r (fun h => zk_not_mem_S m (h ▸ hrS)) (fun h => ok_not_mem_S m (h ▸ hrS))).1]
      · subst hc
        rw [(hXKr r (fun h => zk_not_mem_S m (h ▸ hrS)) (fun h => ok_not_mem_S m (h ▸ hrS))).2,
          (hYKr r (fun h => zk_not_mem_S m (h ▸ hrS)) (fun h => ok_not_mem_S m (h ▸ hrS))).2]
  · by_cases hcS : c ∈ Sset m
    · rcases eq_special_of_not_mem_S hm hrS with hr | hr | hr | hr
      · subst hr
        rw [(hX0c c (fun h => z0_not_mem_S m (h ▸ hcS)) (fun h => o1_not_mem_S m (h ▸ hcS))).1,
          (hY0c c (fun h => z0_not_mem_S m (h ▸ hcS)) (fun h => o1_not_mem_S m (h ▸ hcS))).1]
      · subst hr
        rw [(hX0c c (fun h => z0_not_mem_S m (h ▸ hcS)) (fun h => o1_not_mem_S m (h ▸ hcS))).2,
          (hY0c c (fun h => z0_not_mem_S m (h ▸ hcS)) (fun h => o1_not_mem_S m (h ▸ hcS))).2]
      · subst hr
        rw [(hXKc c (fun h => zk_not_mem_S m (h ▸ hcS)) (fun h => ok_not_mem_S m (h ▸ hcS))).1,
          (hYKc c (fun h => zk_not_mem_S m (h ▸ hcS)) (fun h => ok_not_mem_S m (h ▸ hcS))).1]
      · subst hr
        rw [(hXKc c (fun h => zk_not_mem_S m (h ▸ hcS)) (fun h => ok_not_mem_S m (h ▸ hcS))).2,
          (hYKc c (fun h => zk_not_mem_S m (h ▸ hcS)) (fun h => ok_not_mem_S m (h ▸ hcS))).2]
    · rcases eq_special_of_not_mem_S hm hrS with hr | hr | hr | hr <;>
        rcases eq_special_of_not_mem_S hm hcS with hc | hc | hc | hc <;>
        subst hr <;> subst hc
      all_goals
        first
          | exact hii
          | exact hij
          | exact hki
          | exact hkj
          | rw [hX0b.1, hY0b.1, hij]
          | rw [hX0b.2, hY0b.2, hii, hij]
          | rw [hXKb.1, hYKb.1, hkj]
          | rw [hXKb.2, hYKb.2, hki, hkj]
          | rw [(hX0c (zk m) (z0_ne_zk m hm).symm (o1_ne_zk m hm).symm).1,
              (hY0c (zk m) (z0_ne_zk m hm).symm (o1_ne_zk m hm).symm).1]
          | rw [(hX0c (ok m) (z0_ne_ok m hm).symm (o1_ne_ok m hm).symm).1,
              (hY0c (ok m) (z0_ne_ok m hm).symm (o1_ne_ok m hm).symm).1]
          | rw [(hXKr (o1 m) (o1_ne_zk m hm) (o1_ne_ok m hm)).1,
              (hYKr (o1 m) (o1_ne_zk m hm) (o1_ne_ok m hm)).1]
          | rw [(hXKr (o1 m) (o1_ne_zk m hm) (o1_ne_ok m hm)).2,
              (hYKr (o1 m) (o1_ne_zk m hm) (o1_ne_ok m hm)).2]
          | rw [(hX0r (zk m) (z0_ne_zk m hm).symm (o1_ne_zk m hm).symm).1,
              (hY0r (zk m) (z0_ne_zk m hm).symm (o1_ne_zk m hm).symm).1]
          | rw [(hX0r (zk m) (z0_ne_zk m hm).symm (o1_ne_zk m hm).symm).2,
              (hY0r (zk m) (z0_ne_zk m hm).symm (o1_ne_zk m hm).symm).2]
          | rw [(hX0r (ok m) (z0_ne_ok m hm).symm (o1_ne_ok m hm).symm).1,
              (hY0r (ok m) (z0_ne_ok m hm).symm (o1_ne_ok m hm).symm).1]
          | rw [(hX0r (ok m) (z0_ne_ok m hm).symm (o1_ne_ok m hm).symm).2,
              (hY0r (ok m) (z0_ne_ok m hm).symm (o1_ne_ok m hm).symm).2]

private theorem omega_pow_apply_z0_z0 {m : ℕ} (hm : 3 ≤ m) {a : ℕ} (ha : a ≤ 2) :
    (((((omegaBlock (m + 1 + 1) ⟨0, by omega⟩ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) ^ a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m) (z0 m) (z0 m)) = (if a = 0 then 1 else if a = 1 then 0 else 1) := by
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
  · rw [pow_zero, Matrix.SpecialLinearGroup.coe_one]
    simp [Matrix.one_apply, z0_ne_o1 m, z0_ne_zk m hm, z0_ne_ok m hm, o1_ne_zk m hm,
      o1_ne_ok m hm, zk_ne_ok m, eq_comm]
  · rw [pow_one, coe_omegaBlock_sum]
    simp only [z0, o1, zk, ok, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : z0 m ≠ o1 m := z0_ne_o1 m
    have h2 : z0 m ≠ zk m := z0_ne_zk m hm
    have h3 : z0 m ≠ ok m := z0_ne_ok m hm
    have h4 : o1 m ≠ zk m := o1_ne_zk m hm
    have h5 : o1 m ≠ ok m := o1_ne_ok m hm
    have h6 : zk m ≠ ok m := zk_ne_ok m
    grind [gf2_two]
  · rw [pow_two]
    try rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [coe_omegaBlock_sum, sq_formula (show (⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc ≠ (⟨0, by omega⟩ : Fin (m + 1 + 1)).succ from Fin.castSucc_lt_succ.ne)]
    simp only [z0, o1, zk, ok, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : z0 m ≠ o1 m := z0_ne_o1 m
    have h2 : z0 m ≠ zk m := z0_ne_zk m hm
    have h3 : z0 m ≠ ok m := z0_ne_ok m hm
    have h4 : o1 m ≠ zk m := o1_ne_zk m hm
    have h5 : o1 m ≠ ok m := o1_ne_ok m hm
    have h6 : zk m ≠ ok m := zk_ne_ok m
    grind [gf2_two]
private theorem omega_pow_apply_z0_o1 {m : ℕ} (hm : 3 ≤ m) {a : ℕ} (ha : a ≤ 2) :
    (((((omegaBlock (m + 1 + 1) ⟨0, by omega⟩ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) ^ a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m) (z0 m) (o1 m)) = (if a = 0 then 0 else if a = 1 then 1 else 1) := by
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
  · rw [pow_zero, Matrix.SpecialLinearGroup.coe_one]
    simp [Matrix.one_apply, z0_ne_o1 m, z0_ne_zk m hm, z0_ne_ok m hm, o1_ne_zk m hm,
      o1_ne_ok m hm, zk_ne_ok m, eq_comm]
  · rw [pow_one, coe_omegaBlock_sum]
    simp only [z0, o1, zk, ok, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : z0 m ≠ o1 m := z0_ne_o1 m
    have h2 : z0 m ≠ zk m := z0_ne_zk m hm
    have h3 : z0 m ≠ ok m := z0_ne_ok m hm
    have h4 : o1 m ≠ zk m := o1_ne_zk m hm
    have h5 : o1 m ≠ ok m := o1_ne_ok m hm
    have h6 : zk m ≠ ok m := zk_ne_ok m
    grind [gf2_two]
  · rw [pow_two]
    try rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [coe_omegaBlock_sum, sq_formula (show (⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc ≠ (⟨0, by omega⟩ : Fin (m + 1 + 1)).succ from Fin.castSucc_lt_succ.ne)]
    simp only [z0, o1, zk, ok, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : z0 m ≠ o1 m := z0_ne_o1 m
    have h2 : z0 m ≠ zk m := z0_ne_zk m hm
    have h3 : z0 m ≠ ok m := z0_ne_ok m hm
    have h4 : o1 m ≠ zk m := o1_ne_zk m hm
    have h5 : o1 m ≠ ok m := o1_ne_ok m hm
    have h6 : zk m ≠ ok m := zk_ne_ok m
    grind [gf2_two]
private theorem omegak_pow_apply_zk_zk {m : ℕ} (hm : 3 ≤ m) {a : ℕ} (ha : a ≤ 2) :
    (((((omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) ^ a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m) (zk m) (zk m)) = (if a = 0 then 1 else if a = 1 then 0 else 1) := by
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
  · rw [pow_zero, Matrix.SpecialLinearGroup.coe_one]
    simp [Matrix.one_apply, z0_ne_o1 m, z0_ne_zk m hm, z0_ne_ok m hm, o1_ne_zk m hm,
      o1_ne_ok m hm, zk_ne_ok m, eq_comm]
  · rw [pow_one, coe_omegaBlock_sum]
    simp only [z0, o1, zk, ok, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : z0 m ≠ o1 m := z0_ne_o1 m
    have h2 : z0 m ≠ zk m := z0_ne_zk m hm
    have h3 : z0 m ≠ ok m := z0_ne_ok m hm
    have h4 : o1 m ≠ zk m := o1_ne_zk m hm
    have h5 : o1 m ≠ ok m := o1_ne_ok m hm
    have h6 : zk m ≠ ok m := zk_ne_ok m
    grind [gf2_two]
  · rw [pow_two]
    try rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [coe_omegaBlock_sum, sq_formula (show (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc ≠ (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ from Fin.castSucc_lt_succ.ne)]
    simp only [z0, o1, zk, ok, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : z0 m ≠ o1 m := z0_ne_o1 m
    have h2 : z0 m ≠ zk m := z0_ne_zk m hm
    have h3 : z0 m ≠ ok m := z0_ne_ok m hm
    have h4 : o1 m ≠ zk m := o1_ne_zk m hm
    have h5 : o1 m ≠ ok m := o1_ne_ok m hm
    have h6 : zk m ≠ ok m := zk_ne_ok m
    grind [gf2_two]
private theorem omegak_pow_apply_zk_ok {m : ℕ} (hm : 3 ≤ m) {a : ℕ} (ha : a ≤ 2) :
    (((((omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) ^ a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m) (zk m) (ok m)) = (if a = 0 then 0 else if a = 1 then 1 else 1) := by
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
  · rw [pow_zero, Matrix.SpecialLinearGroup.coe_one]
    simp [Matrix.one_apply, z0_ne_o1 m, z0_ne_zk m hm, z0_ne_ok m hm, o1_ne_zk m hm,
      o1_ne_ok m hm, zk_ne_ok m, eq_comm]
  · rw [pow_one, coe_omegaBlock_sum]
    simp only [z0, o1, zk, ok, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : z0 m ≠ o1 m := z0_ne_o1 m
    have h2 : z0 m ≠ zk m := z0_ne_zk m hm
    have h3 : z0 m ≠ ok m := z0_ne_ok m hm
    have h4 : o1 m ≠ zk m := o1_ne_zk m hm
    have h5 : o1 m ≠ ok m := o1_ne_ok m hm
    have h6 : zk m ≠ ok m := zk_ne_ok m
    grind [gf2_two]
  · rw [pow_two]
    try rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [coe_omegaBlock_sum, sq_formula (show (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc ≠ (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ from Fin.castSucc_lt_succ.ne)]
    simp only [z0, o1, zk, ok, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : z0 m ≠ o1 m := z0_ne_o1 m
    have h2 : z0 m ≠ zk m := z0_ne_zk m hm
    have h3 : z0 m ≠ ok m := z0_ne_ok m hm
    have h4 : o1 m ≠ zk m := o1_ne_zk m hm
    have h5 : o1 m ≠ ok m := o1_ne_ok m hm
    have h6 : zk m ≠ ok m := zk_ne_ok m
    grind [gf2_two]
private theorem omegak_pow_fixes_z0 {m : ℕ} (hm : 3 ≤ m) {a : ℕ} (ha : a ≤ 2) (x : Fin (m + 1 + 1 + 1)) :
    (((((omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) ^ a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m) x (z0 m)) = (if x = z0 m then 1 else 0) := by
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
  · rw [pow_zero, Matrix.SpecialLinearGroup.coe_one]
    simp [Matrix.one_apply, z0_ne_o1 m, z0_ne_zk m hm, z0_ne_ok m hm, o1_ne_zk m hm,
      o1_ne_ok m hm, zk_ne_ok m, eq_comm]
  · rw [pow_one, coe_omegaBlock_sum]
    simp only [z0, o1, zk, ok, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : z0 m ≠ o1 m := z0_ne_o1 m
    have h2 : z0 m ≠ zk m := z0_ne_zk m hm
    have h3 : z0 m ≠ ok m := z0_ne_ok m hm
    have h4 : o1 m ≠ zk m := o1_ne_zk m hm
    have h5 : o1 m ≠ ok m := o1_ne_ok m hm
    have h6 : zk m ≠ ok m := zk_ne_ok m
    grind [gf2_two]
  · rw [pow_two]
    try rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [coe_omegaBlock_sum, sq_formula (show (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc ≠ (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ from Fin.castSucc_lt_succ.ne)]
    simp only [z0, o1, zk, ok, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : z0 m ≠ o1 m := z0_ne_o1 m
    have h2 : z0 m ≠ zk m := z0_ne_zk m hm
    have h3 : z0 m ≠ ok m := z0_ne_ok m hm
    have h4 : o1 m ≠ zk m := o1_ne_zk m hm
    have h5 : o1 m ≠ ok m := o1_ne_ok m hm
    have h6 : zk m ≠ ok m := zk_ne_ok m
    grind [gf2_two]
private theorem omegak_pow_fixes_o1 {m : ℕ} (hm : 3 ≤ m) {a : ℕ} (ha : a ≤ 2) (x : Fin (m + 1 + 1 + 1)) :
    (((((omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) ^ a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m) x (o1 m)) = (if x = o1 m then 1 else 0) := by
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
  · rw [pow_zero, Matrix.SpecialLinearGroup.coe_one]
    simp [Matrix.one_apply, z0_ne_o1 m, z0_ne_zk m hm, z0_ne_ok m hm, o1_ne_zk m hm,
      o1_ne_ok m hm, zk_ne_ok m, eq_comm]
  · rw [pow_one, coe_omegaBlock_sum]
    simp only [z0, o1, zk, ok, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : z0 m ≠ o1 m := z0_ne_o1 m
    have h2 : z0 m ≠ zk m := z0_ne_zk m hm
    have h3 : z0 m ≠ ok m := z0_ne_ok m hm
    have h4 : o1 m ≠ zk m := o1_ne_zk m hm
    have h5 : o1 m ≠ ok m := o1_ne_ok m hm
    have h6 : zk m ≠ ok m := zk_ne_ok m
    grind [gf2_two]
  · rw [pow_two]
    try rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [coe_omegaBlock_sum, sq_formula (show (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc ≠ (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ from Fin.castSucc_lt_succ.ne)]
    simp only [z0, o1, zk, ok, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : z0 m ≠ o1 m := z0_ne_o1 m
    have h2 : z0 m ≠ zk m := z0_ne_zk m hm
    have h3 : z0 m ≠ ok m := z0_ne_ok m hm
    have h4 : o1 m ≠ zk m := o1_ne_zk m hm
    have h5 : o1 m ≠ ok m := o1_ne_ok m hm
    have h6 : zk m ≠ ok m := zk_ne_ok m
    grind [gf2_two]
private theorem omega_pow_fixes_zk {m : ℕ} (hm : 3 ≤ m) {a : ℕ} (ha : a ≤ 2) (x : Fin (m + 1 + 1 + 1)) :
    (((((omegaBlock (m + 1 + 1) ⟨0, by omega⟩ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) ^ a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m) (zk m) x) = (if x = zk m then 1 else 0) := by
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
  · rw [pow_zero, Matrix.SpecialLinearGroup.coe_one]
    simp [Matrix.one_apply, z0_ne_o1 m, z0_ne_zk m hm, z0_ne_ok m hm, o1_ne_zk m hm,
      o1_ne_ok m hm, zk_ne_ok m, eq_comm]
  · rw [pow_one, coe_omegaBlock_sum]
    simp only [z0, o1, zk, ok, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : z0 m ≠ o1 m := z0_ne_o1 m
    have h2 : z0 m ≠ zk m := z0_ne_zk m hm
    have h3 : z0 m ≠ ok m := z0_ne_ok m hm
    have h4 : o1 m ≠ zk m := o1_ne_zk m hm
    have h5 : o1 m ≠ ok m := o1_ne_ok m hm
    have h6 : zk m ≠ ok m := zk_ne_ok m
    grind [gf2_two]
  · rw [pow_two]
    try rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [coe_omegaBlock_sum, sq_formula (show (⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc ≠ (⟨0, by omega⟩ : Fin (m + 1 + 1)).succ from Fin.castSucc_lt_succ.ne)]
    simp only [z0, o1, zk, ok, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : z0 m ≠ o1 m := z0_ne_o1 m
    have h2 : z0 m ≠ zk m := z0_ne_zk m hm
    have h3 : z0 m ≠ ok m := z0_ne_ok m hm
    have h4 : o1 m ≠ zk m := o1_ne_zk m hm
    have h5 : o1 m ≠ ok m := o1_ne_ok m hm
    have h6 : zk m ≠ ok m := zk_ne_ok m
    grind [gf2_two]
private noncomputable def expOf (p q : F2) : ℕ := by
  classical
  exact if p = (1 : F2) then (if q = (0 : F2) then 0 else 2) else 1

private theorem expOf_spec (p q : F2) (hpq : (p, q) ≠ (0, 0)) :
    (if expOf p q = 0 then 1 else if expOf p q = 1 then 0 else 1) = p ∧
    (if expOf p q = 0 then 0 else if expOf p q = 1 then 1 else 1) = q := by
  classical
  rcases f2_eq_zero_or_one p with rfl | rfl <;> rcases f2_eq_zero_or_one q with rfl | rfl
  · exact absurd rfl hpq
  · rw [expOf]; simp
  · rw [expOf]; simp
  · rw [expOf]; simp

theorem eq_omegaBlock_pow_mul_pow {m : ℕ} (hm : 3 ≤ m)
    {d : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (hS : ∀ s ∈ slOn (m + 1 + 1 + 1) {j : Fin (m + 1 + 1 + 1) | 2 ≤ j.val ∧ j.val ≤ m},
      d * s = s * d)
    (h0 : d * omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩ =
      omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩ * d)
    (hk : d * omegaBlock (m + 1 + 1) ⟨m + 1, Nat.lt_succ_self _⟩ =
      omegaBlock (m + 1 + 1) ⟨m + 1, Nat.lt_succ_self _⟩ * d) :
    ∃ p q : ℕ, d = omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩ ^ p *
      omegaBlock (m + 1 + 1) ⟨m + 1, Nat.lt_succ_self _⟩ ^ q := by
  have hS' : ∀ s ∈ slOn (m + 1 + 1 + 1) (Sset m), d * s = s * d := hS
  have hD := shape_facts hm hS' h0 hk
  have hDkeep : ShapeFacts d := hD
  obtain ⟨hDd, hDcr, hD0r, hD0c, hD0b, hDKr, hDKc, hDKb⟩ := hD
  let w0 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 :=
    omegaBlock (m + 1 + 1) ⟨0, by omega⟩
  let wk : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 :=
    omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩
  let p : F2 := (d : MatN m) (z0 m) (z0 m)
  let q : F2 := (d : MatN m) (z0 m) (o1 m)
  let p' : F2 := (d : MatN m) (zk m) (zk m)
  let q' : F2 := (d : MatN m) (zk m) (ok m)
  have hpq : (p, q) ≠ (0, 0) := by
    rintro h
    have hp0 : p = 0 := congrArg Prod.fst h
    have hq0 : q = 0 := congrArg Prod.snd h
    have hrow : ∀ c, (d : MatN m) (z0 m) c = 0 := by
      intro c
      by_cases hcS : c ∈ Sset m
      · exact (hD0c c (fun h => z0_not_mem_S m (h ▸ hcS))
          (fun h => o1_not_mem_S m (h ▸ hcS))).1
      · rcases eq_special_of_not_mem_S hm hcS with hc | hc | hc | hc
        · subst hc; exact hp0
        · subst hc; exact hq0
        · subst hc
          exact (hD0c (zk m) (z0_ne_zk m hm).symm (o1_ne_zk m hm).symm).1
        · subst hc
          exact (hD0c (ok m) (z0_ne_ok m hm).symm (o1_ne_ok m hm).symm).1
    let Din : MatN m := ((d⁻¹ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m)
    have hprod : ((d : MatN m) * Din) (z0 m) (z0 m) = 1 := by
      have h' : (d : MatN m) * Din = 1 := by
        have h := congrArg (fun x : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 => (x : MatN m))
          (mul_inv_cancel d)
        simpa only [Din, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
      rw [h', Matrix.one_apply_eq]
    have hzero : ((d : MatN m) * Din) (z0 m) (z0 m) = 0 := by
      rw [Matrix.mul_apply, Finset.sum_eq_zero]
      intro x _
      rw [hrow x, zero_mul]
    rw [hzero] at hprod
    exact zero_ne_one hprod
  have hp'q' : (p', q') ≠ (0, 0) := by
    rintro h
    have hp0 : p' = 0 := congrArg Prod.fst h
    have hq0 : q' = 0 := congrArg Prod.snd h
    have hrow : ∀ c, (d : MatN m) (zk m) c = 0 := by
      intro c
      by_cases hcS : c ∈ Sset m
      · exact (hDKc c (fun h => zk_not_mem_S m (h ▸ hcS))
          (fun h => ok_not_mem_S m (h ▸ hcS))).1
      · rcases eq_special_of_not_mem_S hm hcS with hc | hc | hc | hc
        · subst hc; exact (hD0r (zk m) (z0_ne_zk m hm).symm (o1_ne_zk m hm).symm).1
        · subst hc; exact (hD0r (zk m) (z0_ne_zk m hm).symm (o1_ne_zk m hm).symm).2
        · subst hc; exact hp0
        · subst hc; exact hq0
    let Din : MatN m := ((d⁻¹ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m)
    have hprod : ((d : MatN m) * Din) (zk m) (zk m) = 1 := by
      have h' : (d : MatN m) * Din = 1 := by
        have h := congrArg (fun x : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 => (x : MatN m))
          (mul_inv_cancel d)
        simpa only [Din, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
      rw [h', Matrix.one_apply_eq]
    have hzero : ((d : MatN m) * Din) (zk m) (zk m) = 0 := by
      rw [Matrix.mul_apply, Finset.sum_eq_zero]
      intro x _
      rw [hrow x, zero_mul]
    rw [hzero] at hprod
    exact zero_ne_one hprod
  let a : ℕ := expOf p q
  let b : ℕ := expOf p' q'
  have ha : a ≤ 2 := by
    simp only [a, expOf]; split_ifs <;> omega
  have hb : b ≤ 2 := by
    simp only [b, expOf]; split_ifs <;> omega
  let Y : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 := w0 ^ a * wk ^ b
  have hcomm : Commute w0 wk :=
    omegaBlock_comm (n := m + 1 + 1) (k := ⟨0, by omega⟩) (k' := ⟨m + 1, by omega⟩) (by simp; omega)
  have hY0 : Y * w0 = w0 * Y := by
    have h2 : Commute (w0 ^ a) w0 := (Commute.refl w0).pow_left a
    have h3 : Commute (wk ^ b) w0 := (hcomm.symm).pow_left b
    exact (h2.mul_left h3).eq
  have hYk : Y * wk = wk * Y := by
    have h2 : Commute (w0 ^ a) wk := hcomm.pow_left a
    have h3 : Commute (wk ^ b) wk := (Commute.refl wk).pow_left b
    exact (h2.mul_left h3).eq
  have hYS : ∀ s ∈ slOn (m + 1 + 1 + 1) (Sset m), Y * s = s * Y := by
    intro s hs
    have h0c : Commute w0 s := by
      have := commute_omegaBlock_slOn (k := ⟨0, by omega⟩) (by
        constructor
        · simpa only [z0] using z0_not_mem_S m
        · simpa only [o1] using o1_not_mem_S m) hs
      change w0 * s = s * w0
      exact this
    have hkc : Commute wk s := by
      have := commute_omegaBlock_slOn (k := ⟨m + 1, by omega⟩) (by
        constructor
        · simpa only [zk] using zk_not_mem_S m
        · simpa only [ok] using ok_not_mem_S m) hs
      change wk * s = s * wk
      exact this
    exact ((h0c.pow_left a).mul_left (hkc.pow_left b)).eq
  have hY := shape_facts hm hYS hY0 hYk
  have hYii : (Y : MatN m) (z0 m) (z0 m) = p := by
    rw [show Y = w0 ^ a * wk ^ b from rfl, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single (z0 m)]
    · rw [omegak_pow_fixes_z0 hm hb (z0 m), if_pos rfl, mul_one,
        omega_pow_apply_z0_z0 hm ha]
      exact (expOf_spec p q hpq).1
    · intro x _ hx
      rw [omegak_pow_fixes_z0 hm hb x, if_neg hx, mul_zero]
    · intro h; exact absurd (Finset.mem_univ (z0 m)) h
  have hYij : (Y : MatN m) (z0 m) (o1 m) = q := by
    rw [show Y = w0 ^ a * wk ^ b from rfl, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single (o1 m)]
    · rw [omegak_pow_fixes_o1 hm hb (o1 m), if_pos rfl, mul_one,
        omega_pow_apply_z0_o1 hm ha]
      exact (expOf_spec p q hpq).2
    · intro x _ hx
      rw [omegak_pow_fixes_o1 hm hb x, if_neg hx, mul_zero]
    · intro h; exact absurd (Finset.mem_univ (o1 m)) h
  have hYki : (Y : MatN m) (zk m) (zk m) = p' := by
    rw [show Y = w0 ^ a * wk ^ b from rfl, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single (zk m)]
    · rw [omega_pow_fixes_zk hm ha (zk m), if_pos rfl, one_mul,
        omegak_pow_apply_zk_zk hm hb]
      exact (expOf_spec p' q' hp'q').1
    · intro x _ hx
      rw [omega_pow_fixes_zk hm ha x, if_neg hx, zero_mul]
    · intro h; exact absurd (Finset.mem_univ (zk m)) h
  have hYkj : (Y : MatN m) (zk m) (ok m) = q' := by
    rw [show Y = w0 ^ a * wk ^ b from rfl, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single (zk m)]
    · rw [omega_pow_fixes_zk hm ha (zk m), if_pos rfl, one_mul,
        omegak_pow_apply_zk_ok hm hb]
      exact (expOf_spec p' q' hp'q').2
    · intro x _ hx
      rw [omega_pow_fixes_zk hm ha x, if_neg hx, zero_mul]
    · intro h; exact absurd (Finset.mem_univ (zk m)) h
  refine ⟨a, b, ?_⟩
  have heq : d = Y := eq_of_params hm hDkeep hY (by rw [hYii]) (by rw [hYij])
    (by rw [hYki]) (by rw [hYkj])
  exact heq

end CFSG.StandardType.GGHalf

end

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigFixA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

open scoped CharTwo

private def s16c11_big_fix_c1_9 : Equiv.Perm (Fin 9) := Equiv.swap 0 1 * Equiv.swap 0 2

private def s16c11_big_fix_c2_9 : Equiv.Perm (Fin 9) := Equiv.swap 3 4 * Equiv.swap 3 5

private abbrev s16c11_big_fix_B_9 : Subgroup (Equiv.Perm (Fin 9)) :=
  Subgroup.closure ({s16c11_big_fix_c1_9, s16c11_big_fix_c2_9} : Set (Equiv.Perm (Fin 9)))

private lemma s16c11_big_fix_isThreeCycle_c1_9 : s16c11_big_fix_c1_9.IsThreeCycle := by
  rw [s16c11_big_fix_c1_9, ← card_support_eq_three_iff]
  decide

private lemma s16c11_big_fix_isThreeCycle_c2_9 : s16c11_big_fix_c2_9.IsThreeCycle := by
  rw [s16c11_big_fix_c2_9, ← card_support_eq_three_iff]
  decide

private def s16c11_big_fix_vec_9 (p : Fin 4 → ZMod 2) : Fin 9 → ZMod 2 :=
  ![p 0, p 0, p 0, p 0 + p 1 + p 2 + p 3, p 0 + p 1 + p 2 + p 3, p 0 + p 1 + p 2 + p 3,
    p 1, p 2, p 3]

private lemma s16c11_big_fix_vec_9_sum (p : Fin 4 → ZMod 2) :
    ∑ i, s16c11_big_fix_vec_9 p i = 0 := by
  simp only [s16c11_big_fix_vec_9, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  ring_nf
  simp [CharTwo.two_eq_zero]

private lemma s16c11_big_fix_vec_9_inv_c1 (p : Fin 4 → ZMod 2) (i : Fin 9) :
    s16c11_big_fix_vec_9 p (s16c11_big_fix_c1_9⁻¹ i) = s16c11_big_fix_vec_9 p i := by
  have hinv : ∀ j, s16c11_big_fix_vec_9 p (s16c11_big_fix_c1_9 j) =
      s16c11_big_fix_vec_9 p j := by
    intro j; fin_cases j <;> rfl
  rw [show s16c11_big_fix_c1_9⁻¹ = s16c11_big_fix_c1_9 ^ 2 by decide]
  simp only [pow_two, Equiv.Perm.mul_apply]
  rw [hinv (s16c11_big_fix_c1_9 i), hinv i]

private lemma s16c11_big_fix_vec_9_inv_c2 (p : Fin 4 → ZMod 2) (i : Fin 9) :
    s16c11_big_fix_vec_9 p (s16c11_big_fix_c2_9⁻¹ i) = s16c11_big_fix_vec_9 p i := by
  have hinv : ∀ j, s16c11_big_fix_vec_9 p (s16c11_big_fix_c2_9 j) =
      s16c11_big_fix_vec_9 p j := by
    intro j; fin_cases j <;> rfl
  rw [show s16c11_big_fix_c2_9⁻¹ = s16c11_big_fix_c2_9 ^ 2 by decide]
  simp only [pow_two, Equiv.Perm.mul_apply]
  rw [hinv (s16c11_big_fix_c2_9 i), hinv i]

private abbrev s16c11_big_fix_canon_9 : Type :=
  {x : Fin 9 → ZMod 2 // (∑ i, x i = 0) ∧
    (∀ i, x (s16c11_big_fix_c1_9⁻¹ i) = x i) ∧
    (∀ i, x (s16c11_big_fix_c2_9⁻¹ i) = x i)}

private def s16c11_big_fix_param_9 (p : Fin 4 → ZMod 2) : s16c11_big_fix_canon_9 :=
  ⟨s16c11_big_fix_vec_9 p, s16c11_big_fix_vec_9_sum p,
    s16c11_big_fix_vec_9_inv_c1 p, s16c11_big_fix_vec_9_inv_c2 p⟩

private def s16c11_big_fix_unparam_9 (x : s16c11_big_fix_canon_9) : Fin 4 → ZMod 2 :=
  ![x.1 0, x.1 6, x.1 7, x.1 8]

private lemma s16c11_big_fix_unparam_9_param_9 (p : Fin 4 → ZMod 2) :
    s16c11_big_fix_unparam_9 (s16c11_big_fix_param_9 p) = p := by
  funext k
  fin_cases k <;> rfl

private lemma s16c11_big_fix_sum_canon_9 {x : Fin 9 → ZMod 2}
    (hx : ∑ i, x i = 0) (h1 : ∀ i, x (s16c11_big_fix_c1_9⁻¹ i) = x i)
    (h2 : ∀ i, x (s16c11_big_fix_c2_9⁻¹ i) = x i) :
    x 3 = x 0 + x 6 + x 7 + x 8 := by
  have h01 : x 0 = x 1 := by
    have := h1 0
    rw [show s16c11_big_fix_c1_9⁻¹ (0 : Fin 9) = 1 by decide] at this
    exact this.symm
  have h12 : x 1 = x 2 := by
    have := h1 1
    rw [show s16c11_big_fix_c1_9⁻¹ (1 : Fin 9) = 2 by decide] at this
    exact this.symm
  have h34 : x 3 = x 4 := by
    have := h2 3
    rw [show s16c11_big_fix_c2_9⁻¹ (3 : Fin 9) = 4 by decide] at this
    exact this.symm
  have h45 : x 4 = x 5 := by
    have := h2 4
    rw [show s16c11_big_fix_c2_9⁻¹ (4 : Fin 9) = 5 by decide] at this
    exact this.symm
  have hsum : ∑ i, x i = x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 + x 8 := by
    simp [Fin.sum_univ_succ]
    abel
  rw [hsum] at hx
  have key : x 0 + x 3 + x 6 + x 7 + x 8 = 0 := by
    have h : x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 + x 8 =
        x 0 + x 3 + x 6 + x 7 + x 8 := by
      rw [h01, h12, h34, h45]
      ring_nf
      simp [CharTwo.two_eq_zero]
    rw [← h]; exact hx
  have hkey2 : x 3 + (x 0 + x 6 + x 7 + x 8) = 0 := by
    simpa [add_comm, add_left_comm, add_assoc] using key
  exact CharTwo.add_eq_zero.mp hkey2

private lemma s16c11_big_fix_param_9_unparam_9 (x : s16c11_big_fix_canon_9) :
    s16c11_big_fix_param_9 (s16c11_big_fix_unparam_9 x) = x := by
  apply Subtype.ext
  funext i
  have h01 : x.1 0 = x.1 1 := by
    have := x.2.2.1 0
    rw [show s16c11_big_fix_c1_9⁻¹ (0 : Fin 9) = 1 by decide] at this
    exact this.symm
  have h12 : x.1 1 = x.1 2 := by
    have := x.2.2.1 1
    rw [show s16c11_big_fix_c1_9⁻¹ (1 : Fin 9) = 2 by decide] at this
    exact this.symm
  have h34 : x.1 3 = x.1 4 := by
    have := x.2.2.2 3
    rw [show s16c11_big_fix_c2_9⁻¹ (3 : Fin 9) = 4 by decide] at this
    exact this.symm
  have h45 : x.1 4 = x.1 5 := by
    have := x.2.2.2 4
    rw [show s16c11_big_fix_c2_9⁻¹ (4 : Fin 9) = 5 by decide] at this
    exact this.symm
  have h3 : x.1 3 = x.1 0 + x.1 6 + x.1 7 + x.1 8 :=
    s16c11_big_fix_sum_canon_9 x.2.1 x.2.2.1 x.2.2.2
  fin_cases i
  · rfl
  · exact h01
  · exact h01.trans h12
  · exact h3.symm
  · exact h3.symm.trans h34
  · exact h3.symm.trans (h34.trans h45)
  · rfl
  · rfl
  · rfl

private lemma s16c11_big_fix_param_9_bijective : Function.Bijective s16c11_big_fix_param_9 := by
  refine ⟨?_, ?_⟩
  · intro p q h
    have := congrArg s16c11_big_fix_unparam_9 h
    rwa [s16c11_big_fix_unparam_9_param_9, s16c11_big_fix_unparam_9_param_9] at this
  · intro x
    exact ⟨s16c11_big_fix_unparam_9 x, s16c11_big_fix_param_9_unparam_9 x⟩

private def s16c11_big_fix_cls_9 :
    s16c11_big_fix_canon_9 → {q : (FFModel.symDn 9).Mod //
      ∀ σ ∈ s16c11_big_fix_B_9, (FFModel.symDn_isActionModel 9).modAct σ q = q} :=
  fun x => ⟨s16c11BigCls 9 x.1 x.2.1, by
    rw [s16c11_big_fix_fixed_iff_closure]
    refine ⟨?_, ?_⟩
    · exact (s16c11_big_fix_class_fixed_iff (n := 9) (σ := s16c11_big_fix_c1_9)
        (by decide) (0 : Fin 9) x.2.1 (s16c11_big_fix_sum_inv _ x.2.1)).mpr x.2.2.1
    · exact (s16c11_big_fix_class_fixed_iff (n := 9) (σ := s16c11_big_fix_c2_9)
        (by decide) (0 : Fin 9) x.2.1 (s16c11_big_fix_sum_inv _ x.2.1)).mpr x.2.2.2⟩

private lemma s16c11_big_fix_cls_9_injective : Function.Injective s16c11_big_fix_cls_9 := by
  intro x y h
  apply Subtype.ext
  have hcls : s16c11BigCls 9 x.1 x.2.1 = s16c11BigCls 9 y.1 y.2.1 :=
    congrArg Subtype.val h
  rw [s16c11BigCls_eq_iff] at hcls
  rcases hcls with hxy | hxy
  · exact hxy.symm
  · exfalso
    have hy' := y.2.1
    rw [hxy] at hy'
    have h1 : (∑ i : Fin 9, (x.1 i + 1)) = (1 : ZMod 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, x.2.1,
        zero_add]
      decide
    have : (1 : ZMod 2) = 0 := by rw [← h1]; exact hy'
    exact one_ne_zero this

private lemma s16c11_big_fix_cls_9_surjective : Function.Surjective s16c11_big_fix_cls_9 := by
  intro q
  obtain ⟨x, hx, hqx⟩ := s16c11BigCls_surjective 9 q.1
  have hq1 : (FFModel.symDn_isActionModel 9).modAct s16c11_big_fix_c1_9 q.1 = q.1 :=
    ((s16c11_big_fix_fixed_iff_closure q.1).mp q.2).1
  have hq2 : (FFModel.symDn_isActionModel 9).modAct s16c11_big_fix_c2_9 q.1 = q.1 :=
    ((s16c11_big_fix_fixed_iff_closure q.1).mp q.2).2
  have hinv1 : ∀ i, x (s16c11_big_fix_c1_9⁻¹ i) = x i := by
    have h' : (FFModel.symDn_isActionModel 9).modAct s16c11_big_fix_c1_9
        (s16c11BigCls 9 x hx) = s16c11BigCls 9 x hx := by rw [← hqx]; exact hq1
    exact (s16c11_big_fix_class_fixed_iff (n := 9) (σ := s16c11_big_fix_c1_9)
      (by decide) (0 : Fin 9) hx (s16c11_big_fix_sum_inv _ hx)).mp h'
  have hinv2 : ∀ i, x (s16c11_big_fix_c2_9⁻¹ i) = x i := by
    have h' : (FFModel.symDn_isActionModel 9).modAct s16c11_big_fix_c2_9
        (s16c11BigCls 9 x hx) = s16c11BigCls 9 x hx := by rw [← hqx]; exact hq2
    exact (s16c11_big_fix_class_fixed_iff (n := 9) (σ := s16c11_big_fix_c2_9)
      (by decide) (0 : Fin 9) hx (s16c11_big_fix_sum_inv _ hx)).mp h'
  exact ⟨⟨x, hx, hinv1, hinv2⟩, Subtype.ext hqx.symm⟩

private lemma s16c11_big_fix_nine :
    ∃ B : Subgroup (Equiv.Perm (Fin 9)), B ≤ alternatingGroup (Fin 9) ∧
      IsPGroup 3 ↥B ∧ ¬ IsCyclic ↥B ∧
      Nat.card {q : (FFModel.symDn 9).Mod // ∀ σ ∈ B,
        (FFModel.symDn_isActionModel 9).modAct σ q = q} = 16 := by
  refine ⟨s16c11_big_fix_B_9, ?_, ?_, ?_, ?_⟩
  · exact s16c11_big_fix_closure_le_alternating s16c11_big_fix_isThreeCycle_c1_9
      s16c11_big_fix_isThreeCycle_c2_9
  · exact s16c11_big_fix_isPGroup_closure (by decide) (by decide) (by decide)
  · exact s16c11_big_fix_not_isCyclic_closure (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hb : Function.Bijective s16c11_big_fix_cls_9 :=
      ⟨s16c11_big_fix_cls_9_injective, s16c11_big_fix_cls_9_surjective⟩
    have e : {q : (FFModel.symDn 9).Mod // ∀ σ ∈ s16c11_big_fix_B_9,
        (FFModel.symDn_isActionModel 9).modAct σ q = q} ≃ (Fin 4 → ZMod 2) :=
      (Equiv.ofBijective s16c11_big_fix_cls_9 hb).symm.trans
        (Equiv.ofBijective s16c11_big_fix_param_9 s16c11_big_fix_param_9_bijective).symm
    calc Nat.card {q : (FFModel.symDn 9).Mod // ∀ σ ∈ s16c11_big_fix_B_9,
          (FFModel.symDn_isActionModel 9).modAct σ q = q}
        = Nat.card (Fin 4 → ZMod 2) := Nat.card_congr e
      _ = Nat.card (ZMod 2) ^ Nat.card (Fin 4) := Nat.card_fun
      _ = 16 := by rw [Nat.card_zmod, Nat.card_fin]; norm_num

private def s16c11_big_fix_c1_10 : Equiv.Perm (Fin 10) := Equiv.swap 0 1 * Equiv.swap 0 2

private def s16c11_big_fix_c2_10 : Equiv.Perm (Fin 10) := Equiv.swap 3 4 * Equiv.swap 3 5

private abbrev s16c11_big_fix_B_10 : Subgroup (Equiv.Perm (Fin 10)) :=
  Subgroup.closure ({s16c11_big_fix_c1_10, s16c11_big_fix_c2_10} : Set (Equiv.Perm (Fin 10)))

private lemma s16c11_big_fix_isThreeCycle_c1_10 : s16c11_big_fix_c1_10.IsThreeCycle := by
  rw [s16c11_big_fix_c1_10, ← card_support_eq_three_iff]
  decide

private lemma s16c11_big_fix_isThreeCycle_c2_10 : s16c11_big_fix_c2_10.IsThreeCycle := by
  rw [s16c11_big_fix_c2_10, ← card_support_eq_three_iff]
  decide

private def s16c11_big_fix_vec_10 (p : Fin 4 → ZMod 2) : Fin 10 → ZMod 2 :=
  ![0, 0, 0, p 0 + p 1 + p 2 + p 3, p 0 + p 1 + p 2 + p 3, p 0 + p 1 + p 2 + p 3,
    p 0, p 1, p 2, p 3]

private lemma s16c11_big_fix_vec_10_sum (p : Fin 4 → ZMod 2) :
    ∑ i, s16c11_big_fix_vec_10 p i = 0 := by
  simp only [s16c11_big_fix_vec_10, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  ring_nf
  simp [CharTwo.two_eq_zero]

private lemma s16c11_big_fix_vec_10_inv_c1 (p : Fin 4 → ZMod 2) (i : Fin 10) :
    s16c11_big_fix_vec_10 p (s16c11_big_fix_c1_10⁻¹ i) = s16c11_big_fix_vec_10 p i := by
  have hinv : ∀ j, s16c11_big_fix_vec_10 p (s16c11_big_fix_c1_10 j) =
      s16c11_big_fix_vec_10 p j := by
    intro j; fin_cases j <;> rfl
  rw [show s16c11_big_fix_c1_10⁻¹ = s16c11_big_fix_c1_10 ^ 2 by decide]
  simp only [pow_two, Equiv.Perm.mul_apply]
  rw [hinv (s16c11_big_fix_c1_10 i), hinv i]

private lemma s16c11_big_fix_vec_10_inv_c2 (p : Fin 4 → ZMod 2) (i : Fin 10) :
    s16c11_big_fix_vec_10 p (s16c11_big_fix_c2_10⁻¹ i) = s16c11_big_fix_vec_10 p i := by
  have hinv : ∀ j, s16c11_big_fix_vec_10 p (s16c11_big_fix_c2_10 j) =
      s16c11_big_fix_vec_10 p j := by
    intro j; fin_cases j <;> rfl
  rw [show s16c11_big_fix_c2_10⁻¹ = s16c11_big_fix_c2_10 ^ 2 by decide]
  simp only [pow_two, Equiv.Perm.mul_apply]
  rw [hinv (s16c11_big_fix_c2_10 i), hinv i]

private abbrev s16c11_big_fix_canon_10 : Type :=
  {x : Fin 10 → ZMod 2 // (∑ i, x i = 0) ∧
    (∀ i, x (s16c11_big_fix_c1_10⁻¹ i) = x i) ∧
    (∀ i, x (s16c11_big_fix_c2_10⁻¹ i) = x i) ∧ x 0 = 0}

private def s16c11_big_fix_param_10 (p : Fin 4 → ZMod 2) : s16c11_big_fix_canon_10 :=
  ⟨s16c11_big_fix_vec_10 p, s16c11_big_fix_vec_10_sum p,
    s16c11_big_fix_vec_10_inv_c1 p, s16c11_big_fix_vec_10_inv_c2 p, rfl⟩

private def s16c11_big_fix_unparam_10 (x : s16c11_big_fix_canon_10) : Fin 4 → ZMod 2 :=
  ![x.1 6, x.1 7, x.1 8, x.1 9]

private lemma s16c11_big_fix_unparam_10_param_10 (p : Fin 4 → ZMod 2) :
    s16c11_big_fix_unparam_10 (s16c11_big_fix_param_10 p) = p := by
  funext k
  fin_cases k <;> rfl

private lemma s16c11_big_fix_sum_canon_10 {x : Fin 10 → ZMod 2}
    (hx : ∑ i, x i = 0) (h0 : x 0 = 0)
    (h1 : ∀ i, x (s16c11_big_fix_c1_10⁻¹ i) = x i)
    (h2 : ∀ i, x (s16c11_big_fix_c2_10⁻¹ i) = x i) :
    x 3 = x 6 + x 7 + x 8 + x 9 := by
  have h01 : x 0 = x 1 := by
    have := h1 0
    rw [show s16c11_big_fix_c1_10⁻¹ (0 : Fin 10) = 1 by decide] at this
    exact this.symm
  have h12 : x 1 = x 2 := by
    have := h1 1
    rw [show s16c11_big_fix_c1_10⁻¹ (1 : Fin 10) = 2 by decide] at this
    exact this.symm
  have h34 : x 3 = x 4 := by
    have := h2 3
    rw [show s16c11_big_fix_c2_10⁻¹ (3 : Fin 10) = 4 by decide] at this
    exact this.symm
  have h45 : x 4 = x 5 := by
    have := h2 4
    rw [show s16c11_big_fix_c2_10⁻¹ (4 : Fin 10) = 5 by decide] at this
    exact this.symm
  have hsum : ∑ i, x i =
      x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 + x 8 + x 9 := by
    simp [Fin.sum_univ_succ]
    abel
  rw [hsum] at hx
  have key : x 0 + x 3 + x 6 + x 7 + x 8 + x 9 = 0 := by
    have h : x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 + x 8 + x 9 =
        x 0 + x 3 + x 6 + x 7 + x 8 + x 9 := by
      rw [h01, h12, h34, h45]
      ring_nf
      simp [CharTwo.two_eq_zero]
    rw [← h]; exact hx
  rw [h0, zero_add] at key
  have hkey2 : x 3 + (x 6 + x 7 + x 8 + x 9) = 0 := by
    simpa [add_comm, add_left_comm, add_assoc] using key
  exact CharTwo.add_eq_zero.mp hkey2

private lemma s16c11_big_fix_param_10_unparam_10 (x : s16c11_big_fix_canon_10) :
    s16c11_big_fix_param_10 (s16c11_big_fix_unparam_10 x) = x := by
  apply Subtype.ext
  funext i
  have h0 : x.1 0 = 0 := x.2.2.2.2
  have h01 : x.1 0 = x.1 1 := by
    have := x.2.2.1 0
    rw [show s16c11_big_fix_c1_10⁻¹ (0 : Fin 10) = 1 by decide] at this
    exact this.symm
  have h12 : x.1 1 = x.1 2 := by
    have := x.2.2.1 1
    rw [show s16c11_big_fix_c1_10⁻¹ (1 : Fin 10) = 2 by decide] at this
    exact this.symm
  have h34 : x.1 3 = x.1 4 := by
    have := x.2.2.2.1 3
    rw [show s16c11_big_fix_c2_10⁻¹ (3 : Fin 10) = 4 by decide] at this
    exact this.symm
  have h45 : x.1 4 = x.1 5 := by
    have := x.2.2.2.1 4
    rw [show s16c11_big_fix_c2_10⁻¹ (4 : Fin 10) = 5 by decide] at this
    exact this.symm
  have h3 : x.1 3 = x.1 6 + x.1 7 + x.1 8 + x.1 9 :=
    s16c11_big_fix_sum_canon_10 x.2.1 x.2.2.2.2 x.2.2.1 x.2.2.2.1
  fin_cases i
  · exact h0.symm
  · exact (h01.symm.trans h0).symm
  · exact ((h12.symm.trans h01.symm).trans h0).symm
  · exact h3.symm
  · exact h3.symm.trans h34
  · exact h3.symm.trans (h34.trans h45)
  · rfl
  · rfl
  · rfl
  · rfl

private lemma s16c11_big_fix_param_10_bijective : Function.Bijective s16c11_big_fix_param_10 := by
  refine ⟨?_, ?_⟩
  · intro p q h
    have := congrArg s16c11_big_fix_unparam_10 h
    rwa [s16c11_big_fix_unparam_10_param_10, s16c11_big_fix_unparam_10_param_10] at this
  · intro x
    exact ⟨s16c11_big_fix_unparam_10 x, s16c11_big_fix_param_10_unparam_10 x⟩

private def s16c11_big_fix_cls_10 :
    s16c11_big_fix_canon_10 → {q : (FFModel.symDn 10).Mod //
      ∀ σ ∈ s16c11_big_fix_B_10, (FFModel.symDn_isActionModel 10).modAct σ q = q} :=
  fun x => ⟨s16c11BigCls 10 x.1 x.2.1, by
    rw [s16c11_big_fix_fixed_iff_closure]
    refine ⟨?_, ?_⟩
    · exact (s16c11_big_fix_class_fixed_iff (n := 10) (σ := s16c11_big_fix_c1_10)
        (by decide) (0 : Fin 10) x.2.1 (s16c11_big_fix_sum_inv _ x.2.1)).mpr x.2.2.1
    · exact (s16c11_big_fix_class_fixed_iff (n := 10) (σ := s16c11_big_fix_c2_10)
        (by decide) (0 : Fin 10) x.2.1 (s16c11_big_fix_sum_inv _ x.2.1)).mpr x.2.2.2.1⟩

private lemma s16c11_big_fix_cls_10_injective : Function.Injective s16c11_big_fix_cls_10 := by
  intro x y h
  apply Subtype.ext
  have hcls : s16c11BigCls 10 x.1 x.2.1 = s16c11BigCls 10 y.1 y.2.1 :=
    congrArg Subtype.val h
  rw [s16c11BigCls_eq_iff] at hcls
  rcases hcls with hxy | hxy
  · exact hxy.symm
  · exfalso
    have hx0 : x.1 0 = 0 := x.2.2.2.2
    have hy0 : y.1 0 = 0 := y.2.2.2.2
    have hxy0 := congrFun hxy 0
    rw [hx0, zero_add, hy0] at hxy0
    exact one_ne_zero hxy0.symm

private lemma s16c11_big_fix_cls_10_surjective : Function.Surjective s16c11_big_fix_cls_10 := by
  intro q
  obtain ⟨x, hx, hqx⟩ := s16c11BigCls_surjective 10 q.1
  have hq1 : (FFModel.symDn_isActionModel 10).modAct s16c11_big_fix_c1_10 q.1 = q.1 :=
    ((s16c11_big_fix_fixed_iff_closure q.1).mp q.2).1
  have hq2 : (FFModel.symDn_isActionModel 10).modAct s16c11_big_fix_c2_10 q.1 = q.1 :=
    ((s16c11_big_fix_fixed_iff_closure q.1).mp q.2).2
  have hinv1 : ∀ i, x (s16c11_big_fix_c1_10⁻¹ i) = x i := by
    have h' : (FFModel.symDn_isActionModel 10).modAct s16c11_big_fix_c1_10
        (s16c11BigCls 10 x hx) = s16c11BigCls 10 x hx := by rw [← hqx]; exact hq1
    exact (s16c11_big_fix_class_fixed_iff (n := 10) (σ := s16c11_big_fix_c1_10)
      (by decide) (0 : Fin 10) hx (s16c11_big_fix_sum_inv _ hx)).mp h'
  have hinv2 : ∀ i, x (s16c11_big_fix_c2_10⁻¹ i) = x i := by
    have h' : (FFModel.symDn_isActionModel 10).modAct s16c11_big_fix_c2_10
        (s16c11BigCls 10 x hx) = s16c11BigCls 10 x hx := by rw [← hqx]; exact hq2
    exact (s16c11_big_fix_class_fixed_iff (n := 10) (σ := s16c11_big_fix_c2_10)
      (by decide) (0 : Fin 10) hx (s16c11_big_fix_sum_inv _ hx)).mp h'
  let x' : Fin 10 → ZMod 2 := fun i => x i + x 0
  have hx'sum : ∑ i, x' i = 0 := by
    have h : ∑ i, x' i = (Fintype.card (Fin 10) : ZMod 2) * x 0 := by
      simp only [x', Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hx,
        zero_add, nsmul_eq_mul]
    rw [h, show (Fintype.card (Fin 10) : ZMod 2) = 0
      by rw [Fintype.card_fin]; decide, zero_mul]
  have hx'inv1 : ∀ i, x' (s16c11_big_fix_c1_10⁻¹ i) = x' i := by
    intro i; simp only [x', hinv1 i]
  have hx'inv2 : ∀ i, x' (s16c11_big_fix_c2_10⁻¹ i) = x' i := by
    intro i; simp only [x', hinv2 i]
  have hx'0 : x' 0 = 0 := by
    simp only [x']; rw [CharTwo.add_self_eq_zero]
  have hcls : s16c11BigCls 10 x' hx'sum = s16c11BigCls 10 x hx := by
    rcases s16c11_big_fix_zmod_two_eq_zero_or_one (x 0) with hc | hc
    · have hxx : x' = x := by funext i; simp only [x', hc, add_zero]
      simp only [hxx]
    · have hxx : x' = fun i => x i + 1 := by funext i; simp only [x', hc]
      exact (s16c11BigCls_eq_iff.mpr (Or.inr hxx)).symm
  exact ⟨⟨x', hx'sum, hx'inv1, hx'inv2, hx'0⟩, Subtype.ext (hcls.trans hqx.symm)⟩

private lemma s16c11_big_fix_ten :
    ∃ B : Subgroup (Equiv.Perm (Fin 10)), B ≤ alternatingGroup (Fin 10) ∧
      IsPGroup 3 ↥B ∧ ¬ IsCyclic ↥B ∧
      Nat.card {q : (FFModel.symDn 10).Mod // ∀ σ ∈ B,
        (FFModel.symDn_isActionModel 10).modAct σ q = q} = 16 := by
  refine ⟨s16c11_big_fix_B_10, ?_, ?_, ?_, ?_⟩
  · exact s16c11_big_fix_closure_le_alternating s16c11_big_fix_isThreeCycle_c1_10
      s16c11_big_fix_isThreeCycle_c2_10
  · exact s16c11_big_fix_isPGroup_closure (by decide) (by decide) (by decide)
  · exact s16c11_big_fix_not_isCyclic_closure (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hb : Function.Bijective s16c11_big_fix_cls_10 :=
      ⟨s16c11_big_fix_cls_10_injective, s16c11_big_fix_cls_10_surjective⟩
    have e : {q : (FFModel.symDn 10).Mod // ∀ σ ∈ s16c11_big_fix_B_10,
        (FFModel.symDn_isActionModel 10).modAct σ q = q} ≃ (Fin 4 → ZMod 2) :=
      (Equiv.ofBijective s16c11_big_fix_cls_10 hb).symm.trans
        (Equiv.ofBijective s16c11_big_fix_param_10 s16c11_big_fix_param_10_bijective).symm
    calc Nat.card {q : (FFModel.symDn 10).Mod // ∀ σ ∈ s16c11_big_fix_B_10,
          (FFModel.symDn_isActionModel 10).modAct σ q = q}
        = Nat.card (Fin 4 → ZMod 2) := Nat.card_congr e
      _ = Nat.card (ZMod 2) ^ Nat.card (Fin 4) := Nat.card_fun
      _ = 16 := by rw [Nat.card_zmod, Nat.card_fin]; norm_num

theorem s16c11_big_exists_fixed_sixteen {n : ℕ} (hn : n = 9 ∨ n = 10) :
    ∃ B : Subgroup (Equiv.Perm (Fin n)), B ≤ alternatingGroup (Fin n) ∧ IsPGroup 3 ↥B ∧
      ¬ IsCyclic ↥B ∧
      Nat.card {q : (FFModel.symDn n).Mod //
        ∀ σ ∈ B, (FFModel.symDn_isActionModel n).modAct σ q = q} = 16 := by
  rcases hn with rfl | rfl
  · exact s16c11_big_fix_nine
  · exact s16c11_big_fix_ten

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

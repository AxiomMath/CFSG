module

public import CFSG.Quasithin.Background.SimsF5Defs

public section

namespace CFSG.Quasithin.SimsF5

noncomputable section

open Matrix

private theorem xvec_apply (i j : Fin 6) : xvec i j = if j = i then 1 else 0 := by
  simp [xvec, Pi.single_apply]

private theorem bil_coord (u v : V6) : bil u v =
    2 * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 + u 4 * v 4) - 2 * (u 5 * v 5) := by
  simp only [bil, qV, Pi.add_apply]
  ring

private theorem bil_sub_left (u v w : V6) : bil (u - v) w = bil u w - bil v w := by
  simp only [bil_coord, Pi.sub_apply]; ring

private theorem bil_neg_right (u v : V6) : bil u (-v) = -bil u v := by
  have key : ∀ (K : Type) [CommRing K] (a b : Fin 6 → K),
      2 * (a 0 * -b 0 + a 1 * -b 1 + a 2 * -b 2 + a 3 * -b 3 + a 4 * -b 4) - 2 * (a 5 * -b 5)
        = -(2 * (a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3 + a 4 * b 4) - 2 * (a 5 * b 5)) := by
    intro K _ a b; ring
  rw [bil_coord, bil_coord]
  simp only [Pi.neg_apply]
  exact key (ZMod 3) u v

private theorem bil_xvec_xvec_of_ne : ∀ i j : Fin 6, i ≠ j → bil (xvec i) (xvec j) = 0 := by
  decide

private theorem bil_xvec_eq_zero_iff (u : V6) (j : Fin 6) : bil u (xvec j) = 0 ↔ u j = 0 := by
  rw [bil_coord]
  fin_cases j <;> simp [xvec_apply] <;>
    first
    | exact (by decide : ∀ a : ZMod 3, 2 * a - 0 = 0 ↔ a = 0) _
    | exact (by decide : ∀ a : ZMod 3, -(2 * a) = 0 ↔ a = 0) _

private theorem qV_mulVec_of_mem {g : GL6} (hg : g ∈ OVq) (v : V6) :
    qV ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) = qV v :=
  qV_smul_of_mem_isometryCore hg v

private theorem bil_mulVec_of_mem {g : GL6} (hg : g ∈ OVq) (u v : V6) :
    bil ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ u) ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) =
      bil u v := by
  unfold bil
  rw [← Matrix.mulVec_add, qV_mulVec_of_mem hg, qV_mulVec_of_mem hg, qV_mulVec_of_mem hg]

private theorem mulVec_mulVec_of_sq {g : GL6} (hgg : g * g = 1) (v : V6) :
    (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, hgg, Units.val_one, Matrix.one_mulVec]

private theorem eq_of_mulVec_xvec {A B : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (h : ∀ i, A *ᵥ xvec i = B *ᵥ xvec i) : A = B := by
  ext i j
  have := congrFun (h j) i
  simpa [xvec, Matrix.mulVec_single_one] using this

private theorem eq_of_smul_xvec {g h : GL6} (H : ∀ i, g • xvec i = h • xvec i) : g = h :=
  Units.ext (eq_of_mulVec_xvec H)

private theorem mem_commSp_iff (g : GL6) (w : V6) :
    w ∈ commSp g ↔ ∃ v : V6, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v - v = w := by
  simp only [commSp, LinearMap.mem_range, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec]

private theorem mem_fixSp_iff (g : GL6) (v : V6) :
    v ∈ fixSp g ↔ (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v := by
  simp only [fixSp, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec, sub_eq_zero]

private theorem mem_spn_xvec_iff (J : Finset (Fin 6)) (w : V6) :
    w ∈ spn {u | ∃ j ∈ J, u = xvec j} ↔ ∀ i, i ∉ J → w i = 0 := by
  constructor
  · intro hw
    unfold spn at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro i hi
      have hne : i ≠ j := fun h => hi (h ▸ hj)
      rw [xvec_apply, if_neg hne]
    | zero => intro i _; rfl
    | add x y _ _ hx hy => intro i hi; simp only [Pi.add_apply, hx i hi, hy i hi]; exact add_zero _
    | smul c x _ hx => intro i hi; simp only [Pi.smul_apply, hx i hi, smul_eq_mul]; exact mul_zero _
  · intro h
    have hw : w = ∑ j ∈ J, w j • xvec j := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, xvec_apply, mul_ite, mul_one,
        mul_zero]
      by_cases hi : i ∈ J
      · rw [Finset.sum_ite_eq]; simp [hi]
      · rw [Finset.sum_ite_eq]; simp [hi, h i hi]
    rw [hw]
    exact Submodule.sum_mem _ fun j hj =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)

private theorem eJd_of_mem {J : Finset (Fin 6)} {i : Fin 6} (h : i ∈ J) : eJd J i = -1 := by
  unfold eJd; rw [if_pos h]

private theorem eJd_of_not_mem {J : Finset (Fin 6)} {i : Fin 6} (h : i ∉ J) : eJd J i = 1 := by
  unfold eJd; rw [if_neg h]

private theorem eJd_sq (J : Finset (Fin 6)) (i : Fin 6) : eJd J i * eJd J i = 1 := by
  unfold eJd; split_ifs <;> decide

private theorem eJ_mulVec (J : Finset (Fin 6)) (v : V6) :
    ((eJ J : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = fun i => eJd J i * v i := by
  funext i
  exact Matrix.mulVec_diagonal _ _ i

private theorem eJ_mulVec_xvec_of_mem {J : Finset (Fin 6)} {i : Fin 6} (hi : i ∈ J) :
    ((eJ J : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = -xvec i := by
  rw [eJ_mulVec]
  funext k
  show eJd J k * xvec i k = -(xvec i k)
  by_cases hk : k = i
  · subst hk
    rw [eJd_of_mem hi, xvec_apply, if_pos rfl]
    exact (by decide : (-1 : ZMod 3) * 1 = -1)
  · rw [xvec_apply, if_neg hk]
    exact (by decide : ∀ a : ZMod 3, a * 0 = -0) _

private theorem eJ_mulVec_xvec_of_not_mem {J : Finset (Fin 6)} {i : Fin 6} (hi : i ∉ J) :
    ((eJ J : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = xvec i := by
  rw [eJ_mulVec]
  funext k
  show eJd J k * xvec i k = xvec i k
  by_cases hk : k = i
  · subst hk
    rw [eJd_of_not_mem hi, xvec_apply, if_pos rfl]
    exact (by decide : (1 : ZMod 3) * 1 = 1)
  · rw [xvec_apply, if_neg hk]
    exact (by decide : ∀ a : ZMod 3, a * 0 = 0) _

private theorem zm3_neg_one_mul_sub_self (a : ZMod 3) : -1 * a - a = a := by
  revert a; decide

private theorem zm3_eq_zero_of_neg_one_mul (a : ZMod 3) (h : -1 * a = a) : a = 0 := by
  revert a; decide

private theorem five_not_mem_Iset : (5 : Fin 6) ∉ Iset := by decide

private theorem mem_Iset_of_ne_five : ∀ i : Fin 6, i ≠ 5 → i ∈ Iset := by decide

theorem eJ_mem_OVq (J : Finset (Fin 6)) : eJ J ∈ OVq := by
  refine Subgroup.subset_closure ?_
  intro v
  rw [eJ_mulVec]
  have h : ∀ i, (eJd J i * v i) ^ 2 = v i ^ 2 := fun i => by
    rw [mul_pow, sq (eJd J i), eJd_sq, one_mul]
  simp only [qV, h]

theorem eJ_mul_self (J : Finset (Fin 6)) : eJ J * eJ J = 1 :=
  Units.ext (eJ_mat_sq J)

theorem commSp_eJ (J : Finset (Fin 6)) : commSp (eJ J) = spn {w | ∃ j ∈ J, w = xvec j} := by
  ext w
  rw [mem_commSp_iff, mem_spn_xvec_iff]
  constructor
  · rintro ⟨v, rfl⟩ i hi
    rw [eJ_mulVec]
    show eJd J i * v i - v i = 0
    rw [eJd_of_not_mem hi]
    exact (by decide : ∀ a : ZMod 3, 1 * a - a = 0) _
  · intro h
    refine ⟨w, ?_⟩
    rw [eJ_mulVec]
    funext i
    by_cases hi : i ∈ J
    · show eJd J i * w i - w i = w i
      rw [eJd_of_mem hi]
      exact zm3_neg_one_mul_sub_self _
    · show eJd J i * w i - w i = w i
      rw [eJd_of_not_mem hi, h i hi]
      exact (by decide : (1 : ZMod 3) * 0 - 0 = 0)

theorem fixSp_eJ (J : Finset (Fin 6)) (hJ : J ⊆ Iset) :
    fixSp (eJ J) = spn ({x6} ∪ {w | ∃ i ∈ Iset \ J, w = xvec i}) := by
  have hset : ({x6} ∪ {w | ∃ i ∈ Iset \ J, w = xvec i} : Set V6) =
      {w | ∃ j ∈ insert (5 : Fin 6) (Iset \ J), w = xvec j} := by
    ext w
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, Finset.mem_insert]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨5, Or.inl rfl, rfl⟩
      · exact ⟨i, Or.inr hi, rfl⟩
    · rintro ⟨j, hj | hj, rfl⟩
      · subst hj; exact Or.inl rfl
      · exact Or.inr ⟨j, hj, rfl⟩
  rw [hset]
  ext v
  rw [mem_fixSp_iff, mem_spn_xvec_iff, eJ_mulVec]
  constructor
  · intro h i hi
    have hiJ : i ∈ J := by
      by_contra hn
      apply hi
      simp only [Finset.mem_insert, Finset.mem_sdiff]
      by_cases h5 : i = 5
      · exact Or.inl h5
      · exact Or.inr ⟨mem_Iset_of_ne_five i h5, hn⟩
    have := congrFun h i
    rw [eJd_of_mem hiJ] at this
    exact zm3_eq_zero_of_neg_one_mul _ this
  · intro h
    funext i
    by_cases hi : i ∈ J
    · have hni : i ∉ insert (5 : Fin 6) (Iset \ J) := by
        simp only [Finset.mem_insert, Finset.mem_sdiff, not_or, not_and, not_not]
        refine ⟨?_, fun _ => hi⟩
        rintro rfl
        exact five_not_mem_Iset (hJ hi)
      show eJd J i * v i = v i
      rw [eJd_of_mem hi, h i hni]
      exact (by decide : (-1 : ZMod 3) * 0 = 0)
    · show eJd J i * v i = v i
      rw [eJd_of_not_mem hi]
      exact one_mul _

theorem eq_eJ_of_commSp (J : Finset (Fin 6)) :
    ∀ g ∈ OVq, g * g = 1 → commSp g = spn {w | ∃ j ∈ J, w = xvec j} → g = eJ J := by
  intro g hg hgg hc
  have hneg : ∀ w ∈ commSp g, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ w = -w := by
    intro w hw
    obtain ⟨v, rfl⟩ := (mem_commSp_iff g w).1 hw
    rw [Matrix.mulVec_sub, mulVec_mulVec_of_sq hgg]
    exact (neg_sub _ _).symm
  have hxj : ∀ j ∈ J, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec j = -xvec j := by
    intro j hj
    apply hneg
    rw [hc]
    exact Submodule.subset_span ⟨j, hj, rfl⟩
  have hxi : ∀ i, i ∉ J → (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = xvec i := by
    intro i hi
    have hdmem : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i - xvec i ∈ commSp g :=
      (mem_commSp_iff g _).2 ⟨xvec i, rfl⟩
    rw [hc] at hdmem
    have hdJ := (mem_spn_xvec_iff J _).1 hdmem
    have hdj : ∀ j ∈ J, ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i - xvec i) j = 0 := by
      intro j hj
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      have e1 := bil_mulVec_of_mem hg (xvec i) (xvec j)
      rw [hxj j hj, bil_neg_right, bil_xvec_xvec_of_ne i j hij] at e1
      have h1 : bil ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i) (xvec j) = 0 :=
        neg_eq_zero.mp e1
      rw [← bil_xvec_eq_zero_iff, bil_sub_left, h1, bil_xvec_xvec_of_ne i j hij]
      exact (by decide : (0 : ZMod 3) - 0 = 0)
    funext k
    by_cases hk : k ∈ J
    · exact sub_eq_zero.mp (hdj k hk)
    · exact sub_eq_zero.mp (hdJ k hk)
  apply eq_of_smul_xvec
  intro i
  show (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i =
    ((eJ J : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i
  by_cases hi : i ∈ J
  · rw [hxj i hi, eJ_mulVec_xvec_of_mem hi]
  · rw [hxi i hi, eJ_mulVec_xvec_of_not_mem hi]

private theorem fMat_mulVec (v : V6) :
    fMat *ᵥ v = ![v 1, v 0, v 2, v 3, v 4, -v 5] := by
  ext i
  fin_cases i <;> simp [fMat, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> exact neg_one_mul _

theorem fDot_mul_self : fDot * fDot = 1 := Units.ext fMat_sq

theorem fDot_smul_x3 : fDot • x3 = x3 := by decide

theorem fDot_smul_x4 : fDot • x4 = x4 := by decide

theorem fDot_smul_x5 : fDot • x5 = x5 := by decide

theorem fDot_smul_x6 : fDot • x6 = -x6 := by decide

theorem fDot_smul_x1 : fDot • x1 = x2 := by decide

private theorem fDot_smul_x2 : fDot • x2 = x1 := by decide

theorem eq_fDot_of (g : GL6) : g * g = 1 → g • x3 = x3 → g • x4 = x4 → g • x5 = x5 →
    g • x6 = -x6 → g • x1 = x2 → g = fDot := by
  intro hgg h3 h4 h5 h6 h1
  have h2 : g • x2 = x1 := by
    rw [← h1, ← mul_smul, hgg, one_smul]
  apply eq_of_smul_xvec
  intro i
  fin_cases i
  · exact h1.trans fDot_smul_x1.symm
  · exact h2.trans fDot_smul_x2.symm
  · exact h3.trans fDot_smul_x3.symm
  · exact h4.trans fDot_smul_x4.symm
  · exact h5.trans fDot_smul_x5.symm
  · exact h6.trans fDot_smul_x6.symm

private theorem mem_V2minus_iff (w : V6) :
    w ∈ V2minus ↔ w 2 = 0 ∧ w 3 = 0 ∧ w 4 = 0 ∧ w 0 + w 1 = 0 := by
  constructor
  · intro hw
    unfold V2minus spn at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · decide
      · decide
    | zero => decide
    | add x y _ _ hx hy =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Pi.add_apply, hx.1, hy.1]; exact add_zero _
      · rw [Pi.add_apply, hx.2.1, hy.2.1]; exact add_zero _
      · rw [Pi.add_apply, hx.2.2.1, hy.2.2.1]; exact add_zero _
      · simp only [Pi.add_apply]; linear_combination hx.2.2.2 + hy.2.2.2
    | smul c x _ hx =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Pi.smul_apply, hx.1]; exact mul_zero _
      · rw [Pi.smul_apply, hx.2.1]; exact mul_zero _
      · rw [Pi.smul_apply, hx.2.2.1]; exact mul_zero _
      · simp only [Pi.smul_apply, smul_eq_mul]; linear_combination c * hx.2.2.2
  · rintro ⟨h2, h3, h4, h01⟩
    have key : ∀ w : V6, w 2 = 0 → w 3 = 0 → w 4 = 0 → w 0 + w 1 = 0 →
        w = w 0 • (x1 - x2) + w 5 • x6 := by decide +kernel
    rw [key w h2 h3 h4 h01]
    unfold V2minus spn
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem V4minus_decomp : ∀ y : V6, y 1 = y 0 → y 5 = 0 →
    y = y 0 • (x1 + x2) + y 2 • x3 + y 3 • x4 + y 4 • x5 := by decide +kernel

private theorem mem_V4minus_iff (w : V6) : w ∈ V4minus ↔ w 1 = w 0 ∧ w 5 = 0 := by
  constructor
  · intro hw
    unfold V4minus spn at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl | rfl
      · decide
      · decide
      · decide
      · decide
    | zero => decide
    | add x y _ _ hx hy =>
      refine ⟨?_, ?_⟩
      · rw [Pi.add_apply, Pi.add_apply, hx.1, hy.1]
      · rw [Pi.add_apply, hx.2, hy.2]; exact add_zero _
    | smul c x _ hx =>
      refine ⟨?_, ?_⟩
      · rw [Pi.smul_apply, Pi.smul_apply, hx.1]
      · rw [Pi.smul_apply, hx.2]; exact mul_zero _
  · rintro ⟨h1, h5⟩
    rw [V4minus_decomp w h1 h5]
    unfold V4minus spn
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem mem_V4plus_iff (w : V6) : w ∈ V4plus ↔ w 4 = 0 ∧ w 5 = 0 := by
  constructor
  · intro hw
    unfold V4plus spn at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl | rfl
      · decide
      · decide
      · decide
      · decide
    | zero => decide
    | add x y _ _ hx hy =>
      refine ⟨?_, ?_⟩
      · rw [Pi.add_apply, hx.1, hy.1]; exact add_zero _
      · rw [Pi.add_apply, hx.2, hy.2]; exact add_zero _
    | smul c x _ hx =>
      refine ⟨?_, ?_⟩
      · rw [Pi.smul_apply, hx.1]; exact mul_zero _
      · rw [Pi.smul_apply, hx.2]; exact mul_zero _
  · rintro ⟨h4, h5⟩
    have key : ∀ w : V6, w 4 = 0 → w 5 = 0 →
        w = w 0 • x1 + w 1 • x2 + w 2 • x3 + w 3 • x4 := by decide +kernel
    rw [key w h4 h5]
    unfold V4plus spn
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem bvec_mem (j : Fin 4) : bvec j ∈ V4minus :=
  (mem_V4minus_iff _).2 ((by decide : ∀ j : Fin 4, bvec j 1 = bvec j 0 ∧ bvec j 5 = 0) j)

private def fv (v : V6) : V6 := ![v 1, v 0, v 2, v 3, v 4, -v 5]

private theorem fMat_mulVec' (v : V6) : fMat *ᵥ v = fv v := fMat_mulVec v

theorem commSp_fDot : commSp fDot = V2minus := by
  ext w
  rw [mem_commSp_iff, mem_V2minus_iff]
  constructor
  · rintro ⟨v, rfl⟩
    show (fMat *ᵥ v - v) 2 = 0 ∧ (fMat *ᵥ v - v) 3 = 0 ∧ (fMat *ᵥ v - v) 4 = 0 ∧
      (fMat *ᵥ v - v) 0 + (fMat *ᵥ v - v) 1 = 0
    rw [fMat_mulVec']
    exact (by decide +kernel : ∀ v : V6, (fv v - v) 2 = 0 ∧ (fv v - v) 3 = 0 ∧ (fv v - v) 4 = 0 ∧
      (fv v - v) 0 + (fv v - v) 1 = 0) v
  · rintro ⟨h2, h3, h4, h01⟩
    refine ⟨![0, w 0, 0, 0, 0, w 5], ?_⟩
    show fMat *ᵥ ![0, w 0, 0, 0, 0, w 5] - ![0, w 0, 0, 0, 0, w 5] = w
    rw [fMat_mulVec']
    exact (by decide +kernel : ∀ w : V6, w 2 = 0 → w 3 = 0 → w 4 = 0 → w 0 + w 1 = 0 →
      fv ![0, w 0, 0, 0, 0, w 5] - ![0, w 0, 0, 0, 0, w 5] = w) w h2 h3 h4 h01

theorem fixSp_fDot : fixSp fDot = V4minus := by
  ext v
  rw [mem_fixSp_iff, mem_V4minus_iff]
  show fMat *ᵥ v = v ↔ _
  rw [fMat_mulVec']
  exact (by decide +kernel : ∀ v : V6, fv v = v ↔ (v 1 = v 0 ∧ v 5 = 0)) v

private theorem linearIndependent_of_dual {n : ℕ} (v : Fin n → V6) (p : Fin n → Fin 6)
    (h : ∀ i j, v j (p i) = if i = j then 1 else 0) : LinearIndependent (ZMod 3) v := by
  refine LinearIndependent.of_comp (LinearMap.pi fun i => LinearMap.proj (R := ZMod 3)
    (φ := fun _ : Fin 6 => ZMod 3) (p i)) ?_
  have : ((LinearMap.pi fun i => LinearMap.proj (R := ZMod 3)
      (φ := fun _ : Fin 6 => ZMod 3) (p i)) ∘ v : Fin n → (Fin n → ZMod 3)) =
      Pi.basisFun (ZMod 3) (Fin n) := by
    funext j i
    simp [h, Pi.basisFun_apply, Pi.single_apply]
  rw [this]
  exact (Pi.basisFun (ZMod 3) (Fin n)).linearIndependent

private theorem range_vec2 (a b : V6) : Set.range ![a, b] = {a, b} := by
  ext w
  simp [Fin.exists_fin_two, eq_comm]
  tauto

private theorem range_vec4 (a b c d : V6) : Set.range ![a, b, c, d] = {a, b, c, d} := by
  ext w
  simp [Fin.exists_fin_succ, eq_comm]
  tauto

private theorem finrank_spn_range {n : ℕ} (v : Fin n → V6) (hv : LinearIndependent (ZMod 3) v) :
    Module.finrank (ZMod 3) (spn (Set.range v)) = n :=
  (finrank_span_eq_card hv).trans (Fintype.card_fin n)

theorem finrank_V2minus : Module.finrank (ZMod 3) V2minus = 2 := by
  have hli : LinearIndependent (ZMod 3) ![x1 - x2, x6] :=
    linearIndependent_of_dual _ ![0, 5] (by decide)
  have h := finrank_spn_range _ hli
  rw [range_vec2] at h
  exact h

theorem finrank_V4minus : Module.finrank (ZMod 3) V4minus = 4 := by
  have hli : LinearIndependent (ZMod 3) bvec := linearIndependent_of_dual _ bidx (by decide)
  have h := finrank_spn_range _ hli
  rw [show bvec = ![x1 + x2, x3, x4, x5] from rfl, range_vec4] at h
  exact h

theorem finrank_V4plus : Module.finrank (ZMod 3) V4plus = 4 := by
  have hli : LinearIndependent (ZMod 3) ![x1, x2, x3, x4] :=
    linearIndependent_of_dual _ ![0, 1, 2, 3] (by decide)
  have h := finrank_spn_range _ hli
  rw [range_vec4] at h
  exact h

private theorem isNondegSub_V2minus : IsNondegSub V2minus := by
  intro w hw hb
  have hW := (mem_V2minus_iff w).1 hw
  have h1 := hb (x1 - x2) ((mem_V2minus_iff _).2 (by decide))
  have h2 := hb x6 ((mem_V2minus_iff _).2 (by decide))
  exact (by decide +kernel : ∀ w : V6, w 2 = 0 → w 3 = 0 → w 4 = 0 → w 0 + w 1 = 0 →
    bil w (x1 - x2) = 0 → bil w x6 = 0 → w = 0) w hW.1 hW.2.1 hW.2.2.1 hW.2.2.2 h1 h2

private theorem isNondegSub_V4minus : IsNondegSub V4minus := by
  intro w hw hb
  have hW := (mem_V4minus_iff w).1 hw
  have h1 := hb (x1 + x2) ((mem_V4minus_iff _).2 (by decide))
  have h3 := hb x3 ((mem_V4minus_iff _).2 (by decide))
  have h4 := hb x4 ((mem_V4minus_iff _).2 (by decide))
  have h5 := hb x5 ((mem_V4minus_iff _).2 (by decide))
  exact (by decide +kernel : ∀ w : V6, w 1 = w 0 → w 5 = 0 → bil w (x1 + x2) = 0 →
    bil w x3 = 0 → bil w x4 = 0 → bil w x5 = 0 → w = 0) w hW.1 hW.2 h1 h3 h4 h5

private theorem isNondegSub_V4plus : IsNondegSub V4plus := by
  intro w hw hb
  have hW := (mem_V4plus_iff w).1 hw
  have h1 := hb x1 ((mem_V4plus_iff _).2 (by decide))
  have h2 := hb x2 ((mem_V4plus_iff _).2 (by decide))
  have h3 := hb x3 ((mem_V4plus_iff _).2 (by decide))
  have h4 := hb x4 ((mem_V4plus_iff _).2 (by decide))
  exact (by decide +kernel : ∀ w : V6, w 4 = 0 → w 5 = 0 → bil w x1 = 0 → bil w x2 = 0 →
    bil w x3 = 0 → bil w x4 = 0 → w = 0) w hW.1 hW.2 h1 h2 h3 h4

private theorem no_tsing_V2minus (U : Sub6) (hUW : U ≤ V2minus) (hs : ∀ u ∈ U, qV u = 0) :
    U = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  have hW := (mem_V2minus_iff u).1 (hUW hu)
  have key : ∀ u : V6, u 2 = 0 → u 3 = 0 → u 4 = 0 → u 0 + u 1 = 0 → qV u = 0 → u = 0 := by
    decide +kernel
  exact (Submodule.mem_bot _).2 (key u hW.1 hW.2.1 hW.2.2.1 hW.2.2.2 (hs u hu))

theorem signMinus_V2minus : SignMinus V2minus := by
  refine ⟨isNondegSub_V2minus, ?_, ?_⟩
  · rw [finrank_V2minus]; decide
  · rintro ⟨U, hUW, hs, hdim⟩
    rw [no_tsing_V2minus U hUW hs, finrank_bot, finrank_V2minus] at hdim
    omega

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
private theorem singular_pair_check : ∀ a b c d a' b' c' d' : ZMod 3,
    a ^ 2 + a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 - 0 ^ 2 = 0 →
    a' ^ 2 + a' ^ 2 + b' ^ 2 + c' ^ 2 + d' ^ 2 - 0 ^ 2 = 0 →
    2 * (a * a' + a * a' + b * b' + c * c' + d * d') - 2 * (0 * 0) = 0 →
    (a' = 0 ∧ b' = 0 ∧ c' = 0 ∧ d' = 0) ∨
      ∃ t : ZMod 3, a = t * a' ∧ b = t * b' ∧ c = t * c' ∧ d = t * d' := by
  decide +kernel

private theorem finrank_le_one_of_tsing_V4minus (U : Sub6) (hUW : U ≤ V4minus)
    (hs : ∀ u ∈ U, qV u = 0) : Module.finrank (ZMod 3) U ≤ 1 := by
  by_cases hU : U = ⊥
  · rw [hU, finrank_bot]; exact Nat.zero_le _
  · obtain ⟨u1, hu1U, hu1⟩ := (Submodule.ne_bot_iff U).1 hU
    have hle : U ≤ Submodule.span (ZMod 3) {u1} := by
      intro u hu
      rw [Submodule.mem_span_singleton]
      have hW := (mem_V4minus_iff u).1 (hUW hu)
      have hW1 := (mem_V4minus_iff u1).1 (hUW hu1U)
      have hq : qV u = 0 := hs u hu
      have hq1 : qV u1 = 0 := hs u1 hu1U
      have hb : bil u u1 = 0 := by
        unfold bil
        rw [hs (u + u1) (U.add_mem hu hu1U), hq, hq1]
        exact (by decide : (0 : ZMod 3) - 0 - 0 = 0)
      have hq' : u 0 ^ 2 + u 0 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + u 4 ^ 2 - 0 ^ 2 = 0 := by
        have := hq; unfold qV at this; rw [hW.1, hW.2] at this; exact this
      have hq1' : u1 0 ^ 2 + u1 0 ^ 2 + u1 2 ^ 2 + u1 3 ^ 2 + u1 4 ^ 2 - 0 ^ 2 = 0 := by
        have := hq1; unfold qV at this; rw [hW1.1, hW1.2] at this; exact this
      have hb' : 2 * (u 0 * u1 0 + u 0 * u1 0 + u 2 * u1 2 + u 3 * u1 3 + u 4 * u1 4) -
          2 * (0 * 0) = 0 := by
        have := hb; rw [bil_coord, hW.1, hW.2, hW1.1, hW1.2] at this; exact this
      rcases singular_pair_check _ _ _ _ _ _ _ _ hq' hq1' hb' with h | ⟨t, h0, h2, h3, h4⟩
      · exfalso
        apply hu1
        funext k
        fin_cases k
        · exact h.1
        · exact hW1.1.trans h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2
        · exact hW1.2
      · refine ⟨t, ?_⟩
        funext k
        fin_cases k
        · exact h0.symm
        · show t * u1 1 = u 1
          rw [hW1.1, hW.1]; exact h0.symm
        · exact h2.symm
        · exact h3.symm
        · exact h4.symm
        · show t * u1 5 = u 5
          rw [hW1.2, hW.2]; exact mul_zero t
    have h1 : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {u1}) ≤ 1 := by
      have := finrank_span_le_card (R := ZMod 3) ({u1} : Set V6)
      simpa using this
    exact (Submodule.finrank_mono hle).trans h1

theorem signMinus_V4minus : SignMinus V4minus := by
  refine ⟨isNondegSub_V4minus, ?_, ?_⟩
  · rw [finrank_V4minus]; decide
  · rintro ⟨U, hUW, hs, hdim⟩
    have := finrank_le_one_of_tsing_V4minus U hUW hs
    rw [finrank_V4minus] at hdim
    omega

theorem zDot_mul_self : zDot * zDot = 1 := eJ_mul_self _

theorem commSp_zDot : commSp zDot = V4plus := by
  have h := commSp_eJ ({0, 1, 2, 3} : Finset (Fin 6))
  have hset : {w | ∃ j ∈ ({0, 1, 2, 3} : Finset (Fin 6)), w = xvec j} =
      ({x1, x2, x3, x4} : Set V6) := by
    ext w
    simp only [Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj | hj | hj | hj, rfl⟩ <;> subst hj
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, Or.inl rfl, rfl⟩
      · exact ⟨1, Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨2, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
      · exact ⟨3, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
  rw [hset] at h
  exact h

theorem signPlus_V4plus : SignPlus V4plus := by
  refine ⟨isNondegSub_V4plus, ?_, ?_⟩
  · rw [finrank_V4plus]; decide
  · refine ⟨spn {x1 + x2 + x3, x1 - x2 + x4}, ?_, ?_, ?_⟩
    · unfold spn
      rw [Submodule.span_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact (mem_V4plus_iff _).2 (by decide)
      · exact (mem_V4plus_iff _).2 (by decide)
    · intro u hu
      unfold spn at hu
      rw [Submodule.mem_span_pair] at hu
      obtain ⟨s, t, rfl⟩ := hu
      exact (by decide : ∀ s t : ZMod 3,
        qV (s • (x1 + x2 + x3) + t • (x1 - x2 + x4)) = 0) s t
    · have hli : LinearIndependent (ZMod 3) ![x1 + x2 + x3, x1 - x2 + x4] :=
        linearIndependent_of_dual _ ![2, 3] (by decide)
      have h := finrank_spn_range _ hli
      rw [range_vec2] at h
      rw [h, finrank_V4plus]

theorem neg_zDot_refl : ∃ v ∈ V4minus, qV v ≠ 0 ∧
    ∀ w ∈ V4minus, -(zDot • w) = w - (bil w v * (qV v)⁻¹) • v := by
  refine ⟨x5, (mem_V4minus_iff _).2 (by decide), by decide, ?_⟩
  intro w hw
  have hW := (mem_V4minus_iff w).1 hw
  have hinv : (qV x5)⁻¹ = 1 := by
    have h : qV x5 = 1 := by decide
    rw [h, inv_one]
  rw [hinv]
  exact (by decide +kernel : ∀ w : V6, w 1 = w 0 → w 5 = 0 →
    -(zDot • w) = w - (bil w x5 * 1) • x5) w hW.1 hW.2

theorem tDot_mul_self : tDot * tDot = 1 := eJ_mul_self _

theorem tDot_ne_one : tDot ≠ 1 := by decide

private theorem mem_V4minus_iff_bil (w : V6) :
    w ∈ V4minus ↔ bil w x6 = 0 ∧ bil w (x1 - x2) = 0 := by
  rw [mem_V4minus_iff]
  exact (by decide +kernel : ∀ w : V6, (w 1 = w 0 ∧ w 5 = 0) ↔
    (bil w x6 = 0 ∧ bil w (x1 - x2) = 0)) w

theorem preserves_V4minus (g : GL6) (hg : g ∈ OVq) (hg6 : g • x6 = x6)
    (hg12 : g • (x1 - x2) = x1 - x2) : ∀ w ∈ V4minus, g • w ∈ V4minus := by
  intro w hw
  rw [mem_V4minus_iff_bil] at hw ⊢
  obtain ⟨h6, h12⟩ := hw
  have hg6' : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = x6 := hg6
  have hg12' : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2) = x1 - x2 := hg12
  refine ⟨?_, ?_⟩
  · have := bil_mulVec_of_mem hg w x6
    rw [hg6'] at this
    exact this.trans h6
  · have := bil_mulVec_of_mem hg w (x1 - x2)
    rw [hg12'] at this
    exact this.trans h12

theorem blk4_mul (g h : GL6) (hh : ∀ w ∈ V4minus, h • w ∈ V4minus) :
    blk4 (g * h) = blk4 g * blk4 h := by
  ext i j
  have hy : (h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ bvec j ∈ V4minus := hh _ (bvec_mem j)
  have hy' := (mem_V4minus_iff _).1 hy
  have hdec := V4minus_decomp _ hy'.1 hy'.2
  have hL : blk4 (g * h) i j = ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
      ((h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ bvec j)) (bidx i) := by
    show (((g * h : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ bvec j) (bidx i) = _
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [hL]
  conv_lhs => rw [hdec]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  have e0 : bvec 0 = x1 + x2 := rfl
  have e1 : bvec 1 = x3 := rfl
  have e2 : bvec 2 = x4 := rfl
  have e3 : bvec 3 = x5 := rfl
  have b0 : bidx 0 = 0 := rfl
  have b1 : bidx 1 = 2 := rfl
  have b2 : bidx 2 = 3 := rfl
  have b3 : bidx 3 = 4 := rfl
  simp only [blk4, Matrix.of_apply, e0, e1, e2, e3, b0, b1, b2, b3, Matrix.mulVec_add,
    Pi.add_apply]
  ring

private theorem eq_of_bidx_coords {y z : V6} (hy : y ∈ V4minus) (hz : z ∈ V4minus)
    (h : ∀ i, y (bidx i) = z (bidx i)) : y = z := by
  have hy' := (mem_V4minus_iff y).1 hy
  have hz' := (mem_V4minus_iff z).1 hz
  funext k
  fin_cases k
  · exact h 0
  · exact hy'.1.trans ((h 0).trans hz'.1.symm)
  · exact h 1
  · exact h 2
  · exact h 3
  · exact hy'.2.trans hz'.2.symm

private theorem mulVec_eq_of_add {M N : Matrix (Fin 6) (Fin 6) (ZMod 3)} (c : ZMod 3) {a b : V6}
    (ha : M *ᵥ a = N *ᵥ a) (hb : M *ᵥ b = N *ᵥ b) :
    M *ᵥ (c • (a + b)) = N *ᵥ (c • (a + b)) := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_add, ha, hb]

private theorem mulVec_eq_of_sub {M N : Matrix (Fin 6) (Fin 6) (ZMod 3)} (c : ZMod 3) {a b : V6}
    (ha : M *ᵥ a = N *ᵥ a) (hb : M *ᵥ b = N *ᵥ b) :
    M *ᵥ (c • (a - b)) = N *ᵥ (c • (a - b)) := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_sub, ha, hb]

theorem blk4_inj (g h : GL6) (hg : g ∈ OVq) (hh : h ∈ OVq) (hg6 : g • x6 = x6) (hh6 : h • x6 = x6)
    (hg12 : g • (x1 - x2) = x1 - x2) (hh12 : h • (x1 - x2) = x1 - x2) (hb : blk4 g = blk4 h) :
    g = h := by
  have hgV := preserves_V4minus g hg hg6 hg12
  have hhV := preserves_V4minus h hh hh6 hh12
  have hbv : ∀ j, g • bvec j = h • bvec j := fun j =>
    eq_of_bidx_coords (hgV _ (bvec_mem j)) (hhV _ (bvec_mem j))
      (fun i => congrFun (congrFun hb i) j)
  have e1 : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 + x2) =
      (h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 + x2) := hbv 0
  have e3 : g • x3 = h • x3 := hbv 1
  have e4 : g • x4 = h • x4 := hbv 2
  have e5 : g • x5 = h • x5 := hbv 3
  have e12 : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2) =
      (h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2) := hg12.trans hh12.symm
  have e6 : g • x6 = h • x6 := hg6.trans hh6.symm
  have hx1 : x1 = (2 : ZMod 3) • ((x1 + x2) + (x1 - x2)) := by decide
  have hx2 : x2 = (2 : ZMod 3) • ((x1 + x2) - (x1 - x2)) := by decide
  have f1 : g • x1 = h • x1 := by
    have := mulVec_eq_of_add (2 : ZMod 3) e1 e12
    rw [← hx1] at this
    exact this
  have f2 : g • x2 = h • x2 := by
    have := mulVec_eq_of_sub (2 : ZMod 3) e1 e12
    rw [← hx2] at this
    exact this
  apply eq_of_smul_xvec
  intro i
  fin_cases i
  · exact f1
  · exact f2
  · exact e3
  · exact e4
  · exact e5
  · exact e6

end

end CFSG.Quasithin.SimsF5

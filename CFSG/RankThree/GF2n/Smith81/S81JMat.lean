module

public import CFSG.RankThree.GF2n.Smith81.S81JDefs
public import CFSG.RankThree.GF2n.Smith81.S81BA5Geom

public section

namespace CFSG.RankThree.GF2n.Smith81.S81J

open CFSG.RankThree.GF2n.Smith81.A5Cube Matrix Module
open scoped commutatorElement

variable {K : Type} [Field K]

private theorem transv_mulVec_eq_add (a b : Fin 6) (c : K) (v : Fin 6 → K) :
    Matrix.transvection a b c *ᵥ v = v + Pi.single a (c * v b) := by
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  congr 1

private theorem mat_eq_of_mulVec {A B : Matrix (Fin 6) (Fin 6) K}
    (h : ∀ v : Fin 6 → K, A *ᵥ v = B *ᵥ v) : A = B :=
  Matrix.ext_iff_mulVec.2 h

private theorem units_mul_inv_mul (u : Kˣ) (x : K) : (u : K) * ((u : K)⁻¹ * x) = x := by
  rw [← mul_assoc, mul_inv_cancel₀ u.ne_zero, one_mul]

theorem dg_val (d : Fin 6 → Kˣ) :
    ((dg d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = Matrix.diagonal fun i => (d i : K) :=
  rfl

theorem dg_mul (d d' : Fin 6 → Kˣ) : (dg (d * d') : GL (Fin 6) K) = dg d * dg d' := by
  apply Units.ext
  rw [Units.val_mul, dg_val, dg_val, dg_val, Matrix.diagonal_mul_diagonal]
  congr 1

theorem dg_one : (dg (1 : Fin 6 → Kˣ) : GL (Fin 6) K) = 1 := by
  apply Units.ext
  rw [dg_val, Units.val_one]
  simp

theorem dg_inv (d : Fin 6 → Kˣ) : (dg d : GL (Fin 6) K)⁻¹ = dg d⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [← dg_mul, mul_inv_cancel, dg_one]

theorem det_dg (d : Fin 6 → Kˣ) :
    ((dg d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = ∏ i, (d i : K) := by
  rw [dg_val, Matrix.det_diagonal]

theorem dg_mulVec (d : Fin 6 → Kˣ) (v : Fin 6 → K) :
    ((dg d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec v = fun i => (d i : K) * v i := by
  funext i
  rw [dg_val, Matrix.mulVec_diagonal]

theorem dg_conj_tr (d : Fin 6 → Kˣ) {a b : Fin 6} (hab : a ≠ b) (t : K) :
    dg d * transvGL K a b hab t * (dg d)⁻¹ =
      transvGL K a b hab ((d a : K) * ((d b : K))⁻¹ * t) := by
  rw [dg_inv]
  apply Units.ext
  apply mat_eq_of_mulVec
  intro v
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, transvGL_val, dg_mulVec,
    transv_mulVec_eq_add, Pi.inv_apply, Units.val_inv_eq_inv_val]
  funext i
  by_cases hi : i = a
  · subst hi
    simp [Pi.single_apply]
    rw [mul_add, units_mul_inv_mul]
    ring
  · simp [Pi.single_apply, hi]

theorem pm_mulVec (σ : Equiv.Perm (Fin 6)) (v : Fin 6 → K) :
    ((pm K σ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec v = fun j => v (σ.symm j) := by
  have h : ((pm K σ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = (σ⁻¹).permMatrix K := rfl
  rw [h, Matrix.permMatrix_mulVec]
  rfl

theorem det_pm [CharP K 2] (σ : Equiv.Perm (Fin 6)) :
    ((pm K σ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
  have h : ((pm K σ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = (σ⁻¹).permMatrix K := rfl
  rw [h, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h' | h'
  · rw [h', Units.val_one, Int.cast_one]
  · rw [h', Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, CharTwo.neg_eq]

theorem pm_conj_dg (σ : Equiv.Perm (Fin 6)) (d : Fin 6 → Kˣ) :
    pm K σ * dg d * (pm K σ)⁻¹ = dg (fun i => d (σ.symm i)) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  apply mat_eq_of_mulVec
  intro v
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, pm_mulVec, dg_mulVec]

theorem pm_conj_tr (σ : Equiv.Perm (Fin 6)) {a b : Fin 6} (hab : a ≠ b) (t : K) :
    pm K σ * transvGL K a b hab t * (pm K σ)⁻¹ =
      transvGL K (σ a) (σ b) (σ.injective.ne hab) t := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  apply mat_eq_of_mulVec
  intro v
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, transvGL_val, pm_mulVec,
    transv_mulVec_eq_add]
  funext j
  simp [Pi.single_apply, Equiv.symm_apply_eq]

theorem finrank_Wc (I : Finset (Fin 6)) : finrank K (Wc K I) = I.card := by
  let e : Wc K I ≃ₗ[K] (I → K) :=
    { toFun := fun v (i : I) => (v : Fin 6 → K) (i : Fin 6)
      invFun := fun f => ⟨fun j => if h : j ∈ I then f ⟨j, h⟩ else 0,
        mem_Wc.mpr fun i hi => by simp [hi]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun v => by
        apply Subtype.ext
        funext j
        by_cases h : j ∈ I
        · simp [h]
        · simp [h, mem_Wc.mp v.2 j h]
      right_inv := fun f => by
        funext i
        simp }
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

theorem Wc_map_pm (σ : Equiv.Perm (Fin 6)) (I : Finset (Fin 6)) :
    (Wc K I).map (Matrix.mulVecLin ((pm K σ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) =
      Wc K (I.image σ) := by
  ext v
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_Wc]
    intro j hj
    rw [Matrix.mulVecLin_apply, pm_mulVec]
    apply (mem_Wc.mp hx) (σ.symm j)
    intro hmem
    apply hj
    have h := Finset.mem_image_of_mem σ hmem
    rwa [Equiv.apply_symm_apply] at h
  · intro hv
    refine ⟨fun i => v (σ i), ?_, ?_⟩
    · rw [mem_Wc]
      intro i hi
      apply (mem_Wc.mp hv) (σ i)
      intro hmem
      obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.mp hmem
      exact hi (by rwa [← σ.injective hkeq])
    · rw [Matrix.mulVecLin_apply, pm_mulVec]
      funext j
      simp

theorem dg_Wc_stable (d : Fin 6 → Kˣ) (I : Finset (Fin 6)) {v : Fin 6 → K} (hv : v ∈ Wc K I) :
    ((dg d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec v ∈ Wc K I := by
  rw [dg_mulVec, mem_Wc]
  intro i hi
  simp [mem_Wc.mp hv i hi]

private theorem I0_image_swap_zero : ∀ i : Fin 6, i ∈ I0 → I0.image (Equiv.swap 0 i) = I0 := by
  decide

private theorem I0_image_swap_out :
    ∀ x y : Fin 6, x ∉ I0 → y ∉ I0 → I0.image (Equiv.swap x y) = I0 := by
  decide

theorem exists_perm_image_eq (I : Finset (Fin 6)) (hI : I.card = 3) :
    ∃ σ : Equiv.Perm (Fin 6), I0.image σ = I := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq I0 I ((show I0.card = 3 by decide).trans hI.symm)
  refine ⟨σ, ?_⟩
  rw [← hσ, Finset.map_eq_image]
  rfl

theorem exists_perm_pair (I : Finset (Fin 6)) (hI : I.card = 3) {a b : Fin 6} (hb : b ∈ I)
    (ha : a ∉ I) : ∃ σ : Equiv.Perm (Fin 6), I0.image σ = I ∧ σ 0 = b ∧ σ 3 = a := by
  obtain ⟨σ₀, hσ₀⟩ := exists_perm_image_eq I hI
  have hb' : b ∈ I0.image σ₀ := by rw [hσ₀]; exact hb
  obtain ⟨i, hi, hib⟩ := Finset.mem_image.mp hb'
  obtain ⟨σ₁, hσ₁⟩ : ∃ τ : Equiv.Perm (Fin 6), τ = σ₀ * Equiv.swap 0 i := ⟨_, rfl⟩
  have hσ₁I : I0.image σ₁ = I := by
    rw [hσ₁, Equiv.Perm.coe_mul, ← Finset.image_image, I0_image_swap_zero i hi, hσ₀]
  have hσ₁0 : σ₁ 0 = b := by
    rw [hσ₁, Equiv.Perm.mul_apply, Equiv.swap_apply_left, hib]
  obtain ⟨j, hj⟩ : ∃ j, σ₁ j = a := ⟨σ₁.symm a, σ₁.apply_symm_apply a⟩
  have hjI0 : j ∉ I0 := by
    intro hjmem
    have h := Finset.mem_image_of_mem σ₁ hjmem
    rw [hσ₁I, hj] at h
    exact ha h
  have hj0 : (0 : Fin 6) ≠ j := by
    intro h
    exact hjI0 (by rw [← h]; decide)
  have h3 : (3 : Fin 6) ∉ I0 := by decide
  refine ⟨σ₁ * Equiv.swap 3 j, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.coe_mul, ← Finset.image_image, I0_image_swap_out 3 j h3 hjI0, hσ₁I]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 6) ≠ 3 by decide) hj0,
      hσ₁0]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hj]

private theorem sj_mat_eq {M N : Matrix (Fin 6) (Fin 6) K}
    (h : ∀ v : Fin 6 → K, M *ᵥ v = N *ᵥ v) : M = N := by
  ext i j
  have h' := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using h'

private theorem sj_tr_mulVec {a b : Fin 6} (hab : a ≠ b) (t : K) (v : Fin 6 → K) :
    ((transvGL K a b hab t : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v =
      v + Pi.single a (t * v b) := by
  rw [transvGL_val, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec]
  congr 1

private theorem sj_dg_val (d : Fin 6 → Kˣ) :
    ((dg d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = Matrix.diagonal fun i => (d i : K) :=
  rfl

private theorem sj_pm_val (σ : Equiv.Perm (Fin 6)) :
    ((pm K σ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = σ⁻¹.permMatrix K :=
  rfl

theorem tr_mul_tr {a b : Fin 6} (hab : a ≠ b) (s t : K) :
    transvGL K a b hab s * transvGL K a b hab t = transvGL K a b hab (s + t) := by
  apply Units.ext
  simp only [Units.val_mul, transvGL_val]
  exact Matrix.transvection_mul_transvection_same a b hab s t

theorem tr_zero {a b : Fin 6} (hab : a ≠ b) : transvGL K a b hab (0 : K) = 1 := by
  apply Units.ext
  simp only [transvGL_val, Matrix.transvection_zero, Units.val_one]

theorem tr_inv {a b : Fin 6} (hab : a ≠ b) (t : K) :
    (transvGL K a b hab t)⁻¹ = transvGL K a b hab (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [tr_mul_tr hab, add_neg_cancel, tr_zero hab]

theorem tr_sq [CharP K 2] {a b : Fin 6} (hab : a ≠ b) (t : K) :
    transvGL K a b hab t * transvGL K a b hab t = 1 := by
  rw [tr_mul_tr hab, CharTwo.add_self_eq_zero, tr_zero hab]

theorem det_tr {a b : Fin 6} (hab : a ≠ b) (t : K) :
    ((transvGL K a b hab t : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
  rw [transvGL_val]
  exact Matrix.det_transvection_of_ne a b hab t

theorem dg_cOn_eq [CharP K 2] {a b : Fin 6} (hab : a ≠ b) (c : Kˣ) :
    (dg (cOn a b c) : GL (Fin 6) K) =
      transvGL K a b hab (c : K) * transvGL K b a hab.symm ((c⁻¹ : Kˣ) : K) *
        transvGL K a b hab (c : K) *
      (transvGL K a b hab (1 : K) * transvGL K b a hab.symm (1 : K) * transvGL K a b hab (1 : K)) := by
  have hba : b ≠ a := hab.symm
  have hcd : (c : K) * ((c⁻¹ : Kˣ) : K) = 1 := Units.mul_inv c
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  apply Units.ext
  apply sj_mat_eq
  intro v
  funext i
  simp only [Units.val_mul, sj_dg_val, Matrix.mulVec_diagonal, ← Matrix.mulVec_mulVec,
    sj_tr_mulVec]
  by_cases hia : i = a
  · rw [hia]
    simp only [cOn, Pi.add_apply, Pi.single_apply, hab, hba, eq_self_iff_true, if_true,
      ite_true, if_false, ite_false, ↓reduceIte, one_mul]
    linear_combination (-(2 * v a + 3 * v b + (c : K) * v a + 2 * (c : K) * v b)) * hcd
      + (-(2 * v a + 3 * v b + (c : K) * v a + 3 * (c : K) * v b)) * h2
  · by_cases hib : i = b
    · rw [hib]
      simp only [cOn, Pi.add_apply, Pi.single_apply, hab, hba, eq_self_iff_true, if_true,
        ite_true, if_false, ite_false, ↓reduceIte, one_mul]
      linear_combination (-(v a)) * hcd
        + (-(v a + v b + ((c⁻¹ : Kˣ) : K) * v a + ((c⁻¹ : Kˣ) : K) * v b
            + ((c⁻¹ : Kˣ) : K) * (c : K) * v b)) * h2
    · simp [cOn, Pi.single_apply, hia, hib, hab, hba]

theorem swap_eq [CharP K 2] {a b : Fin 6} (hab : a ≠ b) :
    transvGL K a b hab (1 : K) * transvGL K b a hab.symm (1 : K) * transvGL K a b hab (1 : K) =
      pm K (Equiv.swap a b) := by
  have hba : b ≠ a := hab.symm
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  apply Units.ext
  apply sj_mat_eq
  intro v
  funext i
  simp only [Units.val_mul, sj_pm_val, Matrix.permMatrix_mulVec, Equiv.swap_inv,
    ← Matrix.mulVec_mulVec, sj_tr_mulVec, Function.comp_apply]
  by_cases hia : i = a
  · rw [hia]
    simp only [Pi.add_apply, Pi.single_apply, hab, hba, eq_self_iff_true, if_true,
      ite_true, if_false, ite_false, ↓reduceIte, one_mul, Equiv.swap_apply_left]
    linear_combination (v a + v b) * h2
  · by_cases hib : i = b
    · rw [hib]
      simp only [Pi.add_apply, Pi.single_apply, hab, hba, eq_self_iff_true, if_true,
        ite_true, if_false, ite_false, ↓reduceIte, one_mul, Equiv.swap_apply_right]
      linear_combination (v b) * h2
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
      simp [Pi.single_apply, hia, hib, hab, hba]

theorem tr_Wc_stable {a b : Fin 6} (hab : a ≠ b) (t : K) {I : Finset (Fin 6)}
    (h : b ∈ I → a ∈ I) {v : Fin 6 → K} (hv : v ∈ Wc K I) :
    ((transvGL K a b hab t : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec v ∈ Wc K I := by
  rw [sj_tr_mulVec, mem_Wc]
  rw [mem_Wc] at hv
  intro i hi
  by_cases hia : i = a
  · have haI : a ∉ I := by rw [← hia]; exact hi
    have hbI : b ∉ I := fun hb => haI (h hb)
    rw [Pi.add_apply, Pi.single_apply, if_pos hia, hv i hi, hv b hbI, mul_zero, zero_add]
  · rw [Pi.add_apply, Pi.single_apply, if_neg hia, hv i hi, add_zero]

theorem tr_mem_UnipGL {a b : Fin 6} (hab : a ≠ b) (t : K) {I : Finset (Fin 6)} (ha : a ∈ I)
    (hb : b ∉ I) : transvGL K a b hab t ∈ UnipGL K (Wc K I) := by
  refine mem_UnipGL_iff.2 ⟨det_tr hab t, fun v => ?_, fun s hs => ?_⟩
  · rw [sj_tr_mulVec, add_sub_cancel_left, mem_Wc]
    intro i hi
    rw [Pi.single_apply]
    split_ifs with hia
    · exact (hi (by rw [hia]; exact ha)).elim
    · rfl
  · rw [sj_tr_mulVec, mem_Wc.1 hs b hb]
    simp

theorem UnipGL_I0_decomp [CharP K 2] {u : GL (Fin 6) K} (hu : u ∈ UnipGL K (Wc K I0)) :
    u * transvGL K 0 3 (by decide) ((u : Matrix (Fin 6) (Fin 6) K) 0 3) ∈ UnipGL K (Wc K I0) ∧
      ∀ v ∈ Wc K ({1, 2, 3} : Finset (Fin 6)),
        ((u * transvGL K 0 3 (by decide) ((u : Matrix (Fin 6) (Fin 6) K) 0 3) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K).mulVec v ∈ Wc K ({1, 2, 3} : Finset (Fin 6)) := by
  obtain ⟨-, hsub, hfix⟩ := mem_UnipGL_iff.1 hu
  have h0 : (0 : Fin 6) ∈ I0 := by decide
  have h1 : (1 : Fin 6) ∈ I0 := by decide
  have h2 : (2 : Fin 6) ∈ I0 := by decide
  have h3 : (3 : Fin 6) ∉ I0 := by decide
  have h4 : (4 : Fin 6) ∉ I0 := by decide
  have h5 : (5 : Fin 6) ∉ I0 := by decide
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hcol : ∀ j ∈ I0, ∀ i, (u : Matrix (Fin 6) (Fin 6) K) i j = if i = j then 1 else 0 := by
    intro j hj i
    have hmem : (Pi.single j (1 : K) : Fin 6 → K) ∈ Wc K I0 := by
      rw [mem_Wc]
      intro k hk
      rw [Pi.single_apply]
      split_ifs with hkj
      · exact (hk (by rw [hkj]; exact hj)).elim
      · rfl
    have := congrFun (hfix _ hmem) i
    simpa [Matrix.mulVec_single_one, Pi.single_apply, Matrix.col_apply] using this
  have hrow : ∀ i, i ∉ I0 → ∀ j, (u : Matrix (Fin 6) (Fin 6) K) i j = if i = j then 1 else 0 := by
    intro i hi j
    have := mem_Wc.1 (hsub (Pi.single j (1 : K))) i hi
    simpa [Matrix.mulVec_single_one, Pi.single_apply, Matrix.col_apply, sub_eq_zero] using this
  have hrowv : ∀ i, i ∉ I0 → ∀ y : Fin 6 → K,
      ((u : Matrix (Fin 6) (Fin 6) K) *ᵥ y) i = y i := by
    intro i hi y
    simp [Matrix.mulVec, dotProduct, hrow i hi, ite_mul]
  have hu00 : (u : Matrix (Fin 6) (Fin 6) K) 0 0 = 1 := by simpa using hcol 0 h0 0
  have hu01 : (u : Matrix (Fin 6) (Fin 6) K) 0 1 = 0 := by simpa using hcol 1 h1 0
  have hu02 : (u : Matrix (Fin 6) (Fin 6) K) 0 2 = 0 := by simpa using hcol 2 h2 0
  refine ⟨mul_mem hu (tr_mem_UnipGL (by decide : (0 : Fin 6) ≠ 3)
    ((u : Matrix (Fin 6) (Fin 6) K) 0 3) h0 h3), fun v hv => ?_⟩
  rw [mem_Wc] at hv
  have hv0 : v 0 = 0 := hv 0 (by decide)
  have hv4 : v 4 = 0 := hv 4 (by decide)
  have hv5 : v 5 = 0 := hv 5 (by decide)
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, sj_tr_mulVec, mem_Wc]
  intro i hi
  rcases (by decide : ∀ i : Fin 6, i ∉ ({1, 2, 3} : Finset (Fin 6)) → i = 0 ∨ i = 4 ∨ i = 5)
    i hi with rfl | rfl | rfl
  · have e30 : (3 : Fin 6) ≠ 0 := by decide
    have e40 : (4 : Fin 6) ≠ 0 := by decide
    have e50 : (5 : Fin 6) ≠ 0 := by decide
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six, hu00, hu01, hu02, Pi.add_apply,
      Pi.single_apply, hv0, hv4, hv5, e30, e40, e50, eq_self_iff_true, if_true, ite_true,
      if_false, ite_false, ↓reduceIte, one_mul, zero_mul, mul_zero, zero_add, add_zero]
    linear_combination ((u : Matrix (Fin 6) (Fin 6) K) 0 3 * v 3) * h2K
  · rw [hrowv 4 h4]
    simp [Pi.single_apply, hv4]
  · rw [hrowv 5 h5]
    simp [Pi.single_apply, hv5]

private theorem transvGL_eq_toGL (a b : Fin 6) (hab : a ≠ b) (t : K) :
    transvGL K a b hab t =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hab t) := by
  rw [transvGL, Matrix.TransvectionStruct.toSpecialLinearGroup_mk]

private theorem transvGL_commutator (a c b : Fin 6) (hac : a ≠ c) (hcb : c ≠ b) (hab : a ≠ b)
    (t : K) :
    ⁅transvGL K a c hac t, transvGL K c b hcb 1⁆ = transvGL K a b hab t := by
  have h := map_commutatorElement
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 6) K →* GL (Fin 6) K)
    (Matrix.SpecialLinearGroup.transvection hac t) (Matrix.SpecialLinearGroup.transvection hcb 1)
  rw [transvGL_eq_toGL, transvGL_eq_toGL, transvGL_eq_toGL, ← h,
    Matrix.SpecialLinearGroup.commutatorElement_transvection, mul_one]

private theorem transvGL_mem_of_dist (H : Subgroup (GL (Fin 6) K))
    (hH : ∀ (a b : Fin 6) (hne : a ≠ b), (a.val + 1 = b.val ∨ b.val + 1 = a.val) →
      ∀ t : K, transvGL K a b hne t ∈ H) (n : ℕ) :
    ∀ (a b : Fin 6) (hne : a ≠ b), (a.val + (n + 1) = b.val ∨ b.val + (n + 1) = a.val) →
      ∀ t : K, transvGL K a b hne t ∈ H := by
  induction n with
  | zero =>
    intro a b hne h t
    exact hH a b hne (by omega) t
  | succ n ih =>
    intro a b hne h t
    have hb := b.isLt
    have ha := a.isLt
    rcases h with h | h
    · obtain ⟨c, hc⟩ : ∃ c : Fin 6, c.val = a.val + 1 := ⟨⟨a.val + 1, by omega⟩, rfl⟩
      have hac : a ≠ c := fun e => by have := congrArg Fin.val e; omega
      have hcb : c ≠ b := fun e => by have := congrArg Fin.val e; omega
      have h1 : transvGL K a c hac t ∈ H := hH a c hac (Or.inl (by omega)) t
      have h2 : transvGL K c b hcb 1 ∈ H := ih c b hcb (Or.inl (by omega)) 1
      rw [← transvGL_commutator a c b hac hcb hne t, commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem h1 h2) (H.inv_mem h1)) (H.inv_mem h2)
    · obtain ⟨c, hc⟩ : ∃ c : Fin 6, c.val = a.val - 1 := ⟨⟨a.val - 1, by omega⟩, rfl⟩
      have hac : a ≠ c := fun e => by have := congrArg Fin.val e; omega
      have hcb : c ≠ b := fun e => by have := congrArg Fin.val e; omega
      have h1 : transvGL K a c hac t ∈ H := hH a c hac (Or.inr (by omega)) t
      have h2 : transvGL K c b hcb 1 ∈ H := ih c b hcb (Or.inr (by omega)) 1
      rw [← transvGL_commutator a c b hac hcb hne t, commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem h1 h2) (H.inv_mem h1)) (H.inv_mem h2)

theorem sl_le_of_adjacent_transvections (H : Subgroup (GL (Fin 6) K))
    (hH : ∀ (a b : Fin 6) (hne : a ≠ b), (a.val + 1 = b.val ∨ b.val + 1 = a.val) →
      ∀ t : K, transvGL K a b hne t ∈ H)
    (g : GL (Fin 6) K) (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1) : g ∈ H := by
  have hall : ∀ (a b : Fin 6) (hne : a ≠ b) (t : K), transvGL K a b hne t ∈ H := by
    intro a b hne t
    have hv : a.val ≠ b.val := fun e => hne (Fin.ext e)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, a.val + (n + 1) = b.val ∨ b.val + (n + 1) = a.val := by
      rcases Nat.lt_or_gt_of_ne hv with h | h
      · exact ⟨b.val - a.val - 1, Or.inl (by omega)⟩
      · exact ⟨a.val - b.val - 1, Or.inr (by omega)⟩
    exact transvGL_mem_of_dist H hH n a b hne hn t
  have hsub := Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin 6) (K := K)
  have hle : Subgroup.closure (Set.range
      (Matrix.TransvectionStruct.toSpecialLinearGroup :
        Matrix.TransvectionStruct (Fin 6) K → Matrix.SpecialLinearGroup (Fin 6) K)) ≤
      H.comap Matrix.SpecialLinearGroup.toGL := by
    rw [Subgroup.closure_le]
    rintro _ ⟨T, rfl⟩
    exact hall T.i T.j T.hij T.c
  rw [hsub, top_le_iff] at hle
  have key : ∀ x : Matrix.SpecialLinearGroup (Fin 6) K, Matrix.SpecialLinearGroup.toGL x ∈ H := by
    intro x
    have hx : x ∈ H.comap Matrix.SpecialLinearGroup.toGL := by
      rw [hle]
      exact Subgroup.mem_top x
    exact hx
  obtain ⟨g', hg'⟩ : ∃ g' : Matrix.SpecialLinearGroup (Fin 6) K,
      Matrix.SpecialLinearGroup.toGL g' = g :=
    ⟨⟨(g : Matrix (Fin 6) (Fin 6) K), hg⟩, Units.ext rfl⟩
  rw [← hg']
  exact key g'

end CFSG.RankThree.GF2n.Smith81.S81J

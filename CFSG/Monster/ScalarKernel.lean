module

public import CFSG.Monster.Code.LatticeCount
public import Mathlib.LinearAlgebra.UnitaryGroup

public noncomputable section

namespace CFSG.Monster.ScalarKernel

open CFSG.Monster CFSG.Monster.Code Matrix

@[expose] def ratVec (u : Fin 24 → ℤ) : Fin 24 → ℚ := fun i => (u i : ℚ)

theorem ratVec_apply (u : Fin 24 → ℤ) (i : Fin 24) : ratVec u i = (u i : ℚ) := rfl

theorem ratVec_injective : Function.Injective ratVec := fun _ _ h =>
  funext fun i => Int.cast_injective (α := ℚ) (congrFun h i)

@[simp] theorem ratVec_zero : ratVec 0 = 0 := by
  funext i; simp [ratVec]

theorem ratVec_add (u v : Fin 24 → ℤ) : ratVec (u + v) = ratVec u + ratVec v := by
  funext i; simp [ratVec]

theorem ratVec_neg (u : Fin 24 → ℤ) : ratVec (-u) = -ratVec u := by
  funext i; simp [ratVec]

theorem codeForm_eq_dotProduct (x y : Fin 24 → ℚ) : codeForm x y = x ⬝ᵥ y / 8 := rfl

theorem codeForm_neg_left (x y : Fin 24 → ℚ) : codeForm (-x) y = -codeForm x y := by
  rw [codeForm_eq_dotProduct, codeForm_eq_dotProduct, neg_dotProduct, neg_div]

theorem codeForm_neg_right (x y : Fin 24 → ℚ) : codeForm x (-y) = -codeForm x y := by
  rw [codeForm_eq_dotProduct, codeForm_eq_dotProduct, dotProduct_neg, neg_div]

theorem codeForm_vecMul_vecMul {g : Matrix (Fin 24) (Fin 24) ℚ} (hg : g * gᵀ = 1)
    (x y : Fin 24 → ℚ) : codeForm (x ᵥ* g) (y ᵥ* g) = codeForm x y := by
  rw [codeForm_eq_dotProduct, codeForm_eq_dotProduct, ← dotProduct_mulVec, ← mulVec_transpose,
    mulVec_mulVec, hg, one_mulVec]

theorem mem_orthogonalGroup_iff_codeForm (g : Matrix (Fin 24) (Fin 24) ℚ) :
    g ∈ orthogonalGroup (Fin 24) ℚ ↔
      ∀ x y : Fin 24 → ℚ, codeForm (x ᵥ* g) (y ᵥ* g) = codeForm x y := by
  rw [mem_orthogonalGroup_iff]
  refine ⟨fun hg => codeForm_vecMul_vecMul hg, fun h => ?_⟩
  ext i j
  have hij := h (Pi.single i 1) (Pi.single j 1)
  rw [codeForm_eq_dotProduct, codeForm_eq_dotProduct, single_one_vecMul, single_one_vecMul,
    div_left_inj' (by norm_num)] at hij
  rw [mul_apply, one_apply]
  simp only [transpose_apply]
  rw [single_dotProduct, one_mul, Pi.single_apply] at hij
  rw [← hij]
  rfl

@[expose] def latticeQ : Set (Fin 24 → ℚ) := ratVec '' codeLattice C

theorem ratVec_mem_latticeQ_iff {u : Fin 24 → ℤ} : ratVec u ∈ latticeQ ↔ u ∈ codeLattice C :=
  ratVec_injective.mem_set_image

@[expose] def latticeO : Subgroup (GL (Fin 24) ℚ) where
  carrier := {g | (g : Matrix (Fin 24) (Fin 24) ℚ) ∈ orthogonalGroup (Fin 24) ℚ ∧
    (fun x => x ᵥ* (g : Matrix (Fin 24) (Fin 24) ℚ)) '' latticeQ = latticeQ}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro g k ⟨hg, hgL⟩ ⟨hk, hkL⟩
    refine ⟨by rw [Units.val_mul]; exact mul_mem hg hk, ?_⟩
    have e : (fun x => x ᵥ* ((g : Matrix (Fin 24) (Fin 24) ℚ) * (k : Matrix (Fin 24) (Fin 24) ℚ)))
        '' latticeQ =
        (fun x => x ᵥ* (k : Matrix (Fin 24) (Fin 24) ℚ)) ''
          ((fun x => x ᵥ* (g : Matrix (Fin 24) (Fin 24) ℚ)) '' latticeQ) := by
      rw [Set.image_image]
      simp only [vecMul_vecMul]
    rw [Units.val_mul, e, hgL, hkL]
  inv_mem' := by
    rintro g ⟨hg, hgL⟩
    have h1 : (g : Matrix (Fin 24) (Fin 24) ℚ) * (g : Matrix (Fin 24) (Fin 24) ℚ)ᵀ = 1 :=
      (mem_orthogonalGroup_iff _ _).1 hg
    have hinv : ((g⁻¹ : GL (Fin 24) ℚ) : Matrix (Fin 24) (Fin 24) ℚ) =
        (g : Matrix (Fin 24) (Fin 24) ℚ)ᵀ := by
      calc ((g⁻¹ : GL (Fin 24) ℚ) : Matrix (Fin 24) (Fin 24) ℚ)
          = ((g⁻¹ : GL (Fin 24) ℚ) : Matrix (Fin 24) (Fin 24) ℚ) *
            ((g : Matrix (Fin 24) (Fin 24) ℚ) * (g : Matrix (Fin 24) (Fin 24) ℚ)ᵀ) := by
            rw [h1, mul_one]
        _ = (g : Matrix (Fin 24) (Fin 24) ℚ)ᵀ := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
    refine ⟨?_, ?_⟩
    · rw [hinv, mem_orthogonalGroup_iff, transpose_transpose]
      exact mul_eq_one_comm.1 h1
    · calc (fun x => x ᵥ* ((g⁻¹ : GL (Fin 24) ℚ) : Matrix (Fin 24) (Fin 24) ℚ)) '' latticeQ
          = (fun x => x ᵥ* ((g⁻¹ : GL (Fin 24) ℚ) : Matrix (Fin 24) (Fin 24) ℚ)) ''
            ((fun x => x ᵥ* (g : Matrix (Fin 24) (Fin 24) ℚ)) '' latticeQ) := by rw [hgL]
        _ = latticeQ := by
            rw [Set.image_image]
            simp only [vecMul_vecMul, Units.mul_inv, vecMul_one, Set.image_id']

@[expose] def mat (g : latticeO) : Matrix (Fin 24) (Fin 24) ℚ :=
  ((g : GL (Fin 24) ℚ) : Matrix (Fin 24) (Fin 24) ℚ)

theorem mat_mul (g k : latticeO) : mat (g * k) = mat g * mat k := rfl

theorem mat_one : mat 1 = 1 := rfl

theorem mat_injective : Function.Injective mat := fun _ _ h =>
  Subtype.ext (Units.ext h)

theorem mat_mem_orthogonalGroup (g : latticeO) : mat g ∈ orthogonalGroup (Fin 24) ℚ := g.2.1

theorem mat_mul_transpose (g : latticeO) : mat g * (mat g)ᵀ = 1 :=
  (mem_orthogonalGroup_iff _ _).1 g.2.1

theorem image_latticeQ (g : latticeO) : (fun x => x ᵥ* mat g) '' latticeQ = latticeQ := g.2.2

@[expose] def negOneO : latticeO :=
  ⟨-1, by
    refine ⟨?_, ?_⟩
    · rw [Units.val_neg, Units.val_one, mem_orthogonalGroup_iff, transpose_neg, transpose_one,
        neg_mul_neg, one_mul]
    · rw [Units.val_neg, Units.val_one]
      ext x
      simp only [vecMul_neg, vecMul_one, Set.mem_image]
      constructor
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨-u, neg_mem_codeLattice allOnes_mem_C hu, ratVec_neg u⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨ratVec (-u), ⟨-u, neg_mem_codeLattice allOnes_mem_C hu, rfl⟩, by
          rw [ratVec_neg, neg_neg]⟩⟩

theorem mat_negOneO : mat negOneO = -1 := by
  rw [mat, negOneO, Units.val_neg, Units.val_one]

@[expose] def latVec (g : Matrix (Fin 24) (Fin 24) ℚ) (u : Fin 24 → ℤ) : Fin 24 → ℤ :=
  fun i => ((ratVec u ᵥ* g) i).num

theorem latVec_spec (g : latticeO) {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    latVec (mat g) u ∈ codeLattice C ∧ ratVec (latVec (mat g) u) = ratVec u ᵥ* mat g := by
  have hx : ratVec u ᵥ* mat g ∈ latticeQ := by
    rw [← image_latticeQ g]
    exact ⟨ratVec u, ⟨u, hu, rfl⟩, rfl⟩
  obtain ⟨v, hv, hvx⟩ := hx
  have e : latVec (mat g) u = v := by
    funext i
    rw [latVec, ← hvx, ratVec_apply, Rat.num_intCast]
  rw [e]
  exact ⟨hv, hvx⟩

@[expose] def latHom (g : latticeO) :
    codeLatticeSubgroup allOnes_mem_C →+ codeLatticeSubgroup allOnes_mem_C where
  toFun u := ⟨latVec (mat g) u, (latVec_spec g u.2).1⟩
  map_zero' := by
    apply Subtype.ext
    apply ratVec_injective
    change ratVec (latVec (mat g) 0) = ratVec 0
    rw [(latVec_spec g zero_mem_codeLattice).2, ratVec_zero, zero_vecMul]
  map_add' u v := by
    apply Subtype.ext
    apply ratVec_injective
    rw [(latVec_spec g (u + v).2).2]
    simp only [AddSubgroup.coe_add, ratVec_add, add_vecMul]
    rw [(latVec_spec g u.2).2, (latVec_spec g v.2).2]

theorem coe_latHom (g : latticeO) (u : codeLatticeSubgroup allOnes_mem_C) :
    ((latHom g u : codeLatticeSubgroup allOnes_mem_C) : Fin 24 → ℤ) = latVec (mat g) u := rfl

theorem ratVec_latHom (g : latticeO) (u : codeLatticeSubgroup allOnes_mem_C) :
    ratVec (latHom g u) = ratVec u ᵥ* mat g :=
  (latVec_spec g u.2).2

theorem latHom_mul (g k : latticeO) (u : codeLatticeSubgroup allOnes_mem_C) :
    latHom (g * k) u = latHom k (latHom g u) := by
  apply Subtype.ext
  apply ratVec_injective
  rw [ratVec_latHom, ratVec_latHom, ratVec_latHom, mat_mul, vecMul_vecMul]

theorem latHom_one (u : codeLatticeSubgroup allOnes_mem_C) : latHom 1 u = u := by
  apply Subtype.ext
  apply ratVec_injective
  rw [ratVec_latHom, mat_one, vecMul_one]

@[expose] def modTwoEnd (g : latticeO) : Module.End (ZMod 2) (codeLatticeModTwo C allOnes_mem_C) :=
  AddMonoidHom.toZModLinearMap 2 (Submodule.mapQ _ _ (latHom g).toIntLinearMap (by
    rintro _ ⟨w, rfl⟩
    refine Submodule.mem_comap.2 ⟨latHom g w, ?_⟩
    simp)).toAddMonoidHom

theorem modTwoEnd_mk (g : latticeO) (u : codeLatticeSubgroup allOnes_mem_C) :
    modTwoEnd g (Submodule.Quotient.mk u) = Submodule.Quotient.mk (latHom g u) := rfl

theorem modTwoEnd_mul (g k : latticeO) : modTwoEnd (g * k) = modTwoEnd k * modTwoEnd g := by
  refine LinearMap.ext fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | H u => rw [Module.End.mul_apply, modTwoEnd_mk, modTwoEnd_mk, modTwoEnd_mk, latHom_mul]

theorem modTwoEnd_one : modTwoEnd 1 = 1 := by
  refine LinearMap.ext fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | H u => rw [modTwoEnd_mk, latHom_one, Module.End.one_apply]

@[expose] def modTwoUnit (g : latticeO) :
    LinearMap.GeneralLinearGroup (ZMod 2) (codeLatticeModTwo C allOnes_mem_C) :=
  ⟨modTwoEnd g, modTwoEnd g⁻¹, by rw [← modTwoEnd_mul, inv_mul_cancel, modTwoEnd_one],
    by rw [← modTwoEnd_mul, mul_inv_cancel, modTwoEnd_one]⟩

@[expose] def modTwoHom :
    latticeO →* (LinearMap.GeneralLinearGroup (ZMod 2) (codeLatticeModTwo C allOnes_mem_C))ᵐᵒᵖ where
  toFun g := MulOpposite.op (modTwoUnit g)
  map_one' := by
    rw [← MulOpposite.op_one]
    congr 1
    exact Units.ext modTwoEnd_one
  map_mul' g k := by
    rw [← MulOpposite.op_mul]
    congr 1
    exact Units.ext (modTwoEnd_mul g k)

theorem modTwoHom_apply (g : latticeO) :
    (((modTwoHom g).unop : LinearMap.GeneralLinearGroup (ZMod 2)
      (codeLatticeModTwo C allOnes_mem_C)) : Module.End (ZMod 2)
        (codeLatticeModTwo C allOnes_mem_C)) = modTwoEnd g := rfl

theorem mem_ker_modTwoHom {g : latticeO} : g ∈ modTwoHom.ker ↔ modTwoEnd g = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have := congrArg (fun x => ((MulOpposite.unop x :
      LinearMap.GeneralLinearGroup (ZMod 2) (codeLatticeModTwo C allOnes_mem_C)) :
        Module.End (ZMod 2) (codeLatticeModTwo C allOnes_mem_C))) h
    exact this
  · intro h
    show MulOpposite.op (modTwoUnit g) = 1
    rw [← MulOpposite.op_one]
    congr 1
    exact Units.ext h

@[expose] def lam (i : Fin 24) : Fin 24 → ℤ := fun j => 1 - 4 * if j = i then 1 else 0

theorem lam_eq_oddMin (i : Fin 24) : lam i = oddMin i 0 := by
  funext j
  simp [lam, oddMin]

theorem lam_mem_minVecs (i : Fin 24) : lam i ∈ minVecs := by
  rw [lam_eq_oddMin]
  exact minFamily₃_subset ⟨i, 0, C.zero_mem, rfl⟩

theorem lam_mem (i : Fin 24) : lam i ∈ codeLattice C := (lam_mem_minVecs i).1

theorem ratVec_lam (i j : Fin 24) : ratVec (lam i) j = 1 - 4 * if j = i then 1 else 0 := by
  simp only [ratVec, lam]
  push_cast
  rfl

theorem codeForm_lam_lam {i j : Fin 24} (hij : i ≠ j) :
    codeForm (ratVec (lam i)) (ratVec (lam j)) = 2 := by
  have e : ∀ k : Fin 24, ratVec (lam i) k * ratVec (lam j) k =
      1 - 4 * (if k = i then 1 else 0) - 4 * (if k = j then 1 else 0) := by
    intro k
    rw [ratVec_lam, ratVec_lam]
    by_cases hi : k = i
    · subst hi
      simp [hij]
    · by_cases hj : k = j
      · subst hj
        simp [hi]
      · simp [hi, hj]
  rw [codeForm, Finset.sum_congr rfl fun k _ => e k, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  norm_num

theorem eq_smul_one_of_lam {g : Matrix (Fin 24) (Fin 24) ℚ} {c : ℚ}
    (h : ∀ i, ratVec (lam i) ᵥ* g = c • ratVec (lam i)) : g = c • 1 := by
  set Λ : Matrix (Fin 24) (Fin 24) ℚ := Matrix.of fun i => ratVec (lam i) with hΛ
  set N : Matrix (Fin 24) (Fin 24) ℚ :=
    Matrix.of fun i k => (1 / 80 : ℚ) * (1 - 20 * if i = k then 1 else 0) with hN
  have hNΛ : N * Λ = 1 := by
    ext i j
    have e : ∀ k : Fin 24, N i k * Λ k j = 1 / 80 - 1 / 4 * (if i = k then 1 else 0) -
        1 / 20 * (if j = k then 1 else 0) + (if i = k then (if j = k then 1 else 0) else 0) := by
      intro k
      rw [hN, hΛ, of_apply, of_apply, ratVec_lam]
      by_cases hi : i = k <;> by_cases hj : j = k <;> simp [hi, hj] <;> norm_num
    rw [mul_apply, Finset.sum_congr rfl fun k _ => e k, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_ite_eq, Finset.sum_ite_eq, Finset.sum_ite_eq, one_apply]
    by_cases hij : i = j
    · subst hij
      simp
      norm_num
    · simp [hij, Ne.symm hij]
      norm_num
  have hΛg : Λ * g = c • Λ := by
    ext i j
    have := congrFun (h i) j
    rw [Matrix.smul_apply, hΛ, of_apply]
    exact this
  calc g = (N * Λ) * g := by rw [hNΛ, one_mul]
    _ = N * (c • Λ) := by rw [mul_assoc, hΛg]
    _ = c • 1 := by rw [Matrix.mul_smul, hNΛ]

theorem classOf_of_mem {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    classOf u = Submodule.Quotient.mk (⟨u, hu⟩ : codeLatticeSubgroup allOnes_mem_C) := by
  rw [classOf, dite_eq_left hu]

theorem latVec_mem_minVecs (g : latticeO) {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    latVec (mat g) u ∈ minVecs := by
  refine ⟨(latVec_spec g hu.1).1, ?_⟩
  change codeForm (ratVec (latVec (mat g) u)) (ratVec (latVec (mat g) u)) = 4
  rw [(latVec_spec g hu.1).2, codeForm_vecMul_vecMul (mat_mul_transpose g)]
  exact hu.2

theorem mat_eq_one_or_neg_one_of_modTwoEnd {g : latticeO} (h : modTwoEnd g = 1) :
    mat g = 1 ∨ mat g = -1 := by
  have hpm : ∀ i, latVec (mat g) (lam i) = lam i ∨ latVec (mat g) (lam i) = -lam i := by
    intro i
    have hc : classOf (latVec (mat g) (lam i)) = classOf (lam i) := by
      rw [classOf_of_mem (latVec_spec g (lam_mem i)).1, classOf_of_mem (lam_mem i)]
      have := LinearMap.congr_fun h
        (Submodule.Quotient.mk (⟨lam i, lam_mem i⟩ : codeLatticeSubgroup allOnes_mem_C))
      rw [modTwoEnd_mk, Module.End.one_apply] at this
      exact this
    exact (classOf_eq_iff (lam_mem_minVecs i) (latVec_mem_minVecs g (lam_mem_minVecs i))).1
      hc.symm
  have hform : ∀ i j, codeForm (ratVec (latVec (mat g) (lam i)))
      (ratVec (latVec (mat g) (lam j))) = codeForm (ratVec (lam i)) (ratVec (lam j)) := by
    intro i j
    rw [(latVec_spec g (lam_mem i)).2, (latVec_spec g (lam_mem j)).2,
      codeForm_vecMul_vecMul (mat_mul_transpose g)]
  have hne : ∀ i, -lam i ≠ lam i := fun i => neg_ne_self_of_mem_minVecs (lam_mem_minVecs i)
  have hsame : ∀ i j, (latVec (mat g) (lam i) = lam i ↔ latVec (mat g) (lam j) = lam j) := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have h2 := codeForm_lam_lam hij
    have hf := hform i j
    rcases hpm i with hi | hi <;> rcases hpm j with hj | hj
    · exact iff_of_true hi hj
    · rw [hi, hj, ratVec_neg, codeForm_neg_right, h2] at hf
      norm_num at hf
    · rw [hi, hj, ratVec_neg, codeForm_neg_left, h2] at hf
      norm_num at hf
    · exact iff_of_false (by rw [hi]; exact hne i) (by rw [hj]; exact hne j)
  by_cases h0 : latVec (mat g) (lam 0) = lam 0
  · left
    have hl : ∀ i, ratVec (lam i) ᵥ* mat g = (1 : ℚ) • ratVec (lam i) := by
      intro i
      rw [← (latVec_spec g (lam_mem i)).2, (hsame i 0).2 h0, one_smul]
    rw [eq_smul_one_of_lam hl, one_smul]
  · right
    have hl : ∀ i, ratVec (lam i) ᵥ* mat g = (-1 : ℚ) • ratVec (lam i) := by
      intro i
      have hi : latVec (mat g) (lam i) = -lam i :=
        (hpm i).resolve_left fun h' => h0 ((hsame i 0).1 h')
      rw [← (latVec_spec g (lam_mem i)).2, hi, ratVec_neg, neg_one_smul]
    rw [eq_smul_one_of_lam hl, neg_one_smul]

theorem modTwoEnd_eq_one_of_mat {g : latticeO} (h : mat g = 1 ∨ mat g = -1) :
    modTwoEnd g = 1 := by
  refine LinearMap.ext fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | H u =>
    rw [modTwoEnd_mk, Module.End.one_apply]
    rcases h with h | h
    · congr 1
      apply Subtype.ext
      apply ratVec_injective
      rw [ratVec_latHom, h, vecMul_one]
    · have e : latHom g u = -u := by
        apply Subtype.ext
        apply ratVec_injective
        rw [ratVec_latHom, h, vecMul_neg, vecMul_one, AddSubgroup.coe_neg, ratVec_neg]
      rw [e, Submodule.Quotient.mk_neg, ZModModule.neg_eq_self]

theorem mem_ker_modTwoHom_iff (g : latticeO) : g ∈ modTwoHom.ker ↔ mat g = 1 ∨ mat g = -1 :=
  mem_ker_modTwoHom.trans ⟨mat_eq_one_or_neg_one_of_modTwoEnd, modTwoEnd_eq_one_of_mat⟩

theorem coe_ker_modTwoHom : (modTwoHom.ker : Set latticeO) = {1, negOneO} := by
  ext g
  rw [SetLike.mem_coe, mem_ker_modTwoHom_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    ← mat_negOneO, ← mat_one, mat_injective.eq_iff, mat_injective.eq_iff]

theorem zpowers_negOneO_eq_ker : Subgroup.zpowers negOneO = modTwoHom.ker := by
  refine le_antisymm (Subgroup.zpowers_le.2 ?_) fun g hg => ?_
  · rw [mem_ker_modTwoHom_iff]
    exact Or.inr mat_negOneO
  · rw [← SetLike.mem_coe, coe_ker_modTwoHom, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

instance : (Subgroup.zpowers negOneO).Normal :=
  zpowers_negOneO_eq_ker ▸ MonoidHom.normal_ker modTwoHom

theorem injective_lift_modTwoHom :
    Function.Injective (QuotientGroup.lift (Subgroup.zpowers negOneO) modTwoHom
      zpowers_negOneO_eq_ker.le) :=
  (QuotientGroup.injective_lift_iff _ _ _).2 zpowers_negOneO_eq_ker

@[expose] def mkO (g : Matrix (Fin 24) (Fin 24) ℚ) (hg : g * gᵀ = 1)
    (hL : (fun x => x ᵥ* g) '' latticeQ = latticeQ) : latticeO :=
  ⟨⟨g, gᵀ, hg, mul_eq_one_comm.1 hg⟩, (mem_orthogonalGroup_iff _ _).2 hg, hL⟩

theorem mat_mkO (g : Matrix (Fin 24) (Fin 24) ℚ) (hg : g * gᵀ = 1)
    (hL : (fun x => x ᵥ* g) '' latticeQ = latticeQ) : mat (mkO g hg hL) = g := rfl

theorem eq_one_or_eq_neg_one_of_classOf {g : Matrix (Fin 24) (Fin 24) ℚ} (hg : g * gᵀ = 1)
    (hL : (fun x => x ᵥ* g) '' latticeQ = latticeQ)
    (htriv : ∀ u v : Fin 24 → ℤ, u ∈ codeLattice C → ratVec v = ratVec u ᵥ* g →
      classOf v = classOf u) : g = 1 ∨ g = -1 := by
  refine mat_eq_one_or_neg_one_of_modTwoEnd (g := mkO g hg hL) (LinearMap.ext fun x => ?_)
  induction x using Submodule.Quotient.induction_on with
  | H u =>
    rw [modTwoEnd_mk, Module.End.one_apply]
    have hs := latVec_spec (mkO g hg hL) u.2
    have h1 := htriv u _ u.2 hs.2
    rwa [classOf_of_mem hs.1, classOf_of_mem u.2] at h1

theorem lattice_mod_two_scalar_kernel :
    (∀ g : Matrix (Fin 24) (Fin 24) ℚ, g ∈ orthogonalGroup (Fin 24) ℚ ↔
      ∀ x y : Fin 24 → ℚ, codeForm (x ᵥ* g) (y ᵥ* g) = codeForm x y) ∧
    (∀ g : GL (Fin 24) ℚ, g ∈ latticeO ↔
      (g : Matrix (Fin 24) (Fin 24) ℚ) ∈ orthogonalGroup (Fin 24) ℚ ∧
        (fun x => x ᵥ* (g : Matrix (Fin 24) (Fin 24) ℚ)) '' latticeQ = latticeQ) ∧
    latticeQ = ratVec '' codeLattice C ∧
    (∀ (g : latticeO) (u : codeLatticeSubgroup allOnes_mem_C),
      ratVec (latHom g u) = ratVec u ᵥ* mat g ∧
      (((modTwoHom g).unop : LinearMap.GeneralLinearGroup (ZMod 2)
        (codeLatticeModTwo C allOnes_mem_C)) : Module.End (ZMod 2)
          (codeLatticeModTwo C allOnes_mem_C)) (Submodule.Quotient.mk u) =
        Submodule.Quotient.mk (latHom g u)) ∧
    (∀ g : latticeO, g ∈ modTwoHom.ker ↔ mat g = 1 ∨ mat g = -1) ∧
    mat negOneO = -1 ∧ (modTwoHom.ker : Set latticeO) = {1, negOneO} ∧
    Subgroup.zpowers negOneO = modTwoHom.ker ∧
    Function.Injective (QuotientGroup.lift (Subgroup.zpowers negOneO) modTwoHom
      zpowers_negOneO_eq_ker.le) :=
  ⟨mem_orthogonalGroup_iff_codeForm, fun _ => Iff.rfl, rfl,
    fun g u => ⟨ratVec_latHom g u, modTwoEnd_mk g u⟩, mem_ker_modTwoHom_iff, mat_negOneO,
    coe_ker_modTwoHom, zpowers_negOneO_eq_ker, injective_lift_modTwoHom⟩

end CFSG.Monster.ScalarKernel

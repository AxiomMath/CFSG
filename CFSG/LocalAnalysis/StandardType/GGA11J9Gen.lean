module

public import CFSG.LocalAnalysis.StandardType.GGA11NbrDefs
public import Certificates.Kernel.ThCent.Leaves

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.A11 Matrix Polynomial

public section

namespace CFSG.StandardType.A11

private noncomputable def j9poly : F2[X] := X ^ 3 + X + 1

private theorem j9poly_natDegree : j9poly.natDegree = 3 := by
  unfold j9poly
  compute_degree!

private theorem F2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  haveI : Fintype F2 := Fintype.ofFinite F2
  have hcard : Fintype.card F2 = 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hx2 : x ^ 2 = x := by
    have := FiniteField.pow_card (K := F2) x
    rwa [hcard] at this
  have hzero : x * (x + 1) = 0 := by
    rw [mul_add, mul_one, ← pow_two, hx2]
    exact CharTwo.add_self_eq_zero x
  rcases mul_eq_zero.mp hzero with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    calc x = x + (1 + 1) := by rw [CharTwo.add_self_eq_zero, add_zero]
      _ = (x + 1) + 1 := by rw [add_assoc]
      _ = 0 + 1 := by rw [h]
      _ = 1 := by rw [zero_add]

private theorem j9poly_irreducible : Irreducible j9poly := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [j9poly_natDegree]
    decide
  · intro x
    rcases F2_eq_zero_or_one x with rfl | rfl
    · intro hx
      simp [Polynomial.IsRoot, j9poly, Polynomial.eval_add, Polynomial.eval_pow,
        Polynomial.eval_X] at hx
    · intro hx
      simp [Polynomial.IsRoot, j9poly, Polynomial.eval_add, Polynomial.eval_pow,
        Polynomial.eval_X, CharTwo.add_self_eq_zero] at hx

private instance : Fact (Irreducible j9poly) := ⟨j9poly_irreducible⟩

private abbrev F8 : Type := AdjoinRoot j9poly

private theorem Om_aeval : Polynomial.aeval Om j9poly = 0 := by
  unfold j9poly
  simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Om, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, pow_succ, pow_zero,
      CharTwo.add_self_eq_zero]

private noncomputable def reg : F8 →+* Matrix (Fin 3) (Fin 3) F2 :=
  Ideal.Quotient.lift (Ideal.span {j9poly}) (Polynomial.aeval Om).toRingHom (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, show (Polynomial.aeval Om).toRingHom j9poly = 0 from Om_aeval, zero_mul])

private theorem reg_root : reg (AdjoinRoot.root j9poly) = Om := by
  rw [← AdjoinRoot.mk_X]
  change (Ideal.Quotient.lift (Ideal.span {j9poly}) (Polynomial.aeval Om).toRingHom _)
    (Ideal.Quotient.mk (Ideal.span {j9poly}) X) = Om
  rw [Ideal.Quotient.lift_mk]
  exact Polynomial.aeval_X Om

private theorem reg_comm (x : F8) : reg x * Om = Om * reg x := by
  rw [← reg_root, ← map_mul, ← map_mul, mul_comm]

private theorem reg_injective : Function.Injective reg := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  have hxunit : IsUnit x := isUnit_iff_ne_zero.mpr hx0
  obtain ⟨y, hy⟩ := hxunit
  rw [← hy] at hx
  have h1 : reg (1 : F8) = 0 := by
    rw [← Units.mul_inv y, map_mul, hx, zero_mul]
  rw [map_one] at h1
  exact one_ne_zero h1

private theorem reg_algebraMap (a : F2) :
    reg (algebraMap F2 F8 a) = algebraMap F2 (Matrix (Fin 3) (Fin 3) F2) a := by
  rw [show algebraMap F2 F8 a = (AdjoinRoot.mk j9poly) (Polynomial.C a) from rfl]
  change (Ideal.Quotient.lift (Ideal.span {j9poly}) (Polynomial.aeval Om).toRingHom _)
    (Ideal.Quotient.mk (Ideal.span {j9poly}) (Polynomial.C a)) = _
  rw [Ideal.Quotient.lift_mk]
  exact Polynomial.aeval_C Om a

private theorem reg_smul (a : F2) (y : F8) : reg (a • y) = a • reg y := by
  rw [Algebra.smul_def, map_mul, reg_algebraMap, ← Algebra.smul_def]

private noncomputable def e0 : Fin 3 → F2 := Pi.single 0 1
private noncomputable def e1 : Fin 3 → F2 := Pi.single 1 1
private noncomputable def e2 : Fin 3 → F2 := Pi.single 2 1

private theorem Om_mulVec_e0 : Om *ᵥ e0 = e1 := by
  rw [show e0 = Pi.single (0 : Fin 3) (1 : F2) from rfl, Matrix.mulVec_single_one]
  ext i
  fin_cases i <;> simp [Om, e1, Matrix.col, Pi.single]

private theorem Om_mulVec_e1 : Om *ᵥ e1 = e2 := by
  rw [show e1 = Pi.single (1 : Fin 3) (1 : F2) from rfl, Matrix.mulVec_single_one]
  ext i
  fin_cases i <;> simp [Om, e2, Matrix.col, Pi.single]

private theorem cyclic_inj (M N : Matrix (Fin 3) (Fin 3) F2)
    (hM : M * Om = Om * M) (hN : N * Om = Om * N) (h : M *ᵥ e0 = N *ᵥ e0) : M = N := by
  have hM1 : M *ᵥ e1 = Om *ᵥ (M *ᵥ e0) := by
    rw [← Om_mulVec_e0, Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec]
  have hN1 : N *ᵥ e1 = Om *ᵥ (N *ᵥ e0) := by
    rw [← Om_mulVec_e0, Matrix.mulVec_mulVec, hN, ← Matrix.mulVec_mulVec]
  have h1 : M *ᵥ e1 = N *ᵥ e1 := by rw [hM1, hN1, h]
  have hM2 : M *ᵥ e2 = Om *ᵥ (M *ᵥ e1) := by
    rw [← Om_mulVec_e1, Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec]
  have hN2 : N *ᵥ e2 = Om *ᵥ (N *ᵥ e1) := by
    rw [← Om_mulVec_e1, Matrix.mulVec_mulVec, hN, ← Matrix.mulVec_mulVec]
  have h2 : M *ᵥ e2 = N *ᵥ e2 := by rw [hM2, hN2, h1]
  ext i j
  fin_cases j
  · have := congrFun h i
    simpa [e0, Matrix.mulVec_single_one] using this
  · have := congrFun h1 i
    simpa [e1, Matrix.mulVec_single_one] using this
  · have := congrFun h2 i
    simpa [e2, Matrix.mulVec_single_one] using this

private theorem reg_surj (M : Matrix (Fin 3) (Fin 3) F2) (hM : M * Om = Om * M) :
    M ∈ reg.range := by
  let w : Fin 3 → F2 := M *ᵥ e0
  let x : F8 := (w 0) • (1 : F8) + (w 1) • AdjoinRoot.root j9poly +
    (w 2) • (AdjoinRoot.root j9poly) ^ 2
  have hx : reg x = w 0 • 1 + w 1 • Om + w 2 • Om ^ 2 := by
    simp only [x, map_add, reg_smul, map_pow, map_one, reg_root]
  have hNcomm : reg x * Om = Om * reg x := by
    rw [← reg_root, ← map_mul, ← map_mul, mul_comm]
  have hNe0 : reg x *ᵥ e0 = w := by
    rw [hx, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, pow_two, ← Matrix.mulVec_mulVec,
      Om_mulVec_e0, Om_mulVec_e1]
    ext i
    fin_cases i <;> simp [e0, e1, e2, w, Matrix.mulVec_single_one, Matrix.col]
  have hMN : M = reg x := cyclic_inj M (reg x) hM hNcomm (by rw [hNe0])
  rw [hMN]
  exact RingHom.mem_range.mpr ⟨x, rfl⟩

private noncomputable def e9Fun : Fin 3 × Fin 3 → Fin 9 :=
  fun p => ![3, 7, 8, 0, 1, 2, 4, 5, 6] (finProdFinEquiv p)

private theorem e9Fun_bijective : Function.Bijective e9Fun := by decide

private noncomputable def e9 : Fin 3 × Fin 3 ≃ Fin 9 :=
  Equiv.ofBijective e9Fun e9Fun_bijective

private noncomputable def bIdx9 (a : Fin 9) : Fin 3 :=
  ⟨(blk (Fin.castLE (by omega) a)).val, by fin_cases a <;> decide⟩

private noncomputable def iIdx9 (a : Fin 9) : Fin 3 := idxIn (Fin.castLE (by omega) a)

private theorem e9_bIdx_iIdx (a : Fin 9) : e9 (bIdx9 a, iIdx9 a) = a := by
  rw [e9, Equiv.ofBijective_apply]
  fin_cases a <;> decide

private theorem e9_symm (a : Fin 9) : e9.symm a = (bIdx9 a, iIdx9 a) := by
  rw [Equiv.symm_apply_eq]
  exact (e9_bIdx_iIdx a).symm

private noncomputable def emb : Matrix (Fin 3) (Fin 3) F8 →+* Matrix (Fin 9) (Fin 9) F2 :=
  (Matrix.reindexRingEquiv F2 e9).toRingHom.comp
    ((Matrix.compRingEquiv (Fin 3) (Fin 3) F2).toRingHom.comp (RingHom.mapMatrix reg))

private theorem emb_apply (A : Matrix (Fin 3) (Fin 3) F8) (a b : Fin 9) :
    emb A a b = reg (A (bIdx9 a) (bIdx9 b)) (iIdx9 a) (iIdx9 b) := by
  change (Matrix.reindexRingEquiv F2 e9)
      ((Matrix.compRingEquiv (Fin 3) (Fin 3) F2) (A.map reg)) a b = _
  rw [Matrix.compRingEquiv_apply]
  change (Matrix.reindex e9 e9
      (Matrix.comp (Fin 3) (Fin 3) (Fin 3) (Fin 3) F2 (A.map reg))) a b = _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.comp_apply, Matrix.map_apply,
    e9_symm, e9_symm]

private theorem blk_castLE (a : Fin 9) :
    blk (Fin.castLE (by omega) a) = (bIdx9 a).castSucc := by
  apply Fin.ext
  rfl

private theorem idxIn_castLE (a : Fin 9) : idxIn (Fin.castLE (by omega) a) = iIdx9 a := rfl

private noncomputable def Ai (i : Fin 3) : Matrix (Fin 3) (Fin 3) F8 :=
  Matrix.of fun p q => if p = q then (if p = i then AdjoinRoot.root j9poly else 1) else 0

private theorem T9mat_formula (i : Fin 3) (a b : Fin 9) :
    T9mat i a b = (if bIdx9 a = i ∧ bIdx9 b = i then Om (iIdx9 a) (iIdx9 b)
      else if a = b then 1 else 0) := by
  unfold T9mat
  simp only [Matrix.of_apply, blk_castLE, idxIn_castLE]
  by_cases h1 : bIdx9 a = i <;> by_cases h2 : bIdx9 b = i <;> by_cases h3 : a = b
  all_goals simp_all [Fin.castSucc_inj]

private theorem e9_eq_of_components (a b : Fin 9) (h1 : bIdx9 a = bIdx9 b)
    (h2 : iIdx9 a = iIdx9 b) : a = b := by
  rw [← e9_bIdx_iIdx a, ← e9_bIdx_iIdx b, h1, h2]

private theorem emb_Ai_apply (i : Fin 3) (a b : Fin 9) :
    emb (Ai i) a b = (if bIdx9 a = i ∧ bIdx9 b = i then Om (iIdx9 a) (iIdx9 b)
      else if a = b then 1 else 0) := by
  rw [emb_apply]
  unfold Ai
  simp only [Matrix.of_apply]
  by_cases h1 : bIdx9 a = i <;> by_cases h2 : bIdx9 b = i
  · simp [h1, h2, reg_root]
  · have hne : bIdx9 a ≠ bIdx9 b := fun h => h2 (h.symm.trans h1)
    have hab : a ≠ b := fun h => hne (by rw [h])
    simp [h1, h2, Ne.symm h2, hne, hab, Matrix.one_apply]
  · have hne : bIdx9 a ≠ bIdx9 b := fun h => h1 (h.trans h2)
    have hab : a ≠ b := fun h => hne (by rw [h])
    simp [h1, h2, Ne.symm h1, hne, hab, Matrix.one_apply]
  · by_cases hb : bIdx9 a = bIdx9 b
    · by_cases hi : iIdx9 a = iIdx9 b
      · have hab : a = b := e9_eq_of_components a b hb hi
        simp [h1, h2, hb, hi, hab]
      · have hab : a ≠ b := fun h => hi (by rw [h])
        simp [h1, h2, hb, hi, hab, Matrix.one_apply]
    · have hab : a ≠ b := fun h => hb (by rw [h])
      simp [h1, h2, hb, hab, Matrix.one_apply]

private theorem emb_Ai (i : Fin 3) : emb (Ai i) = T9mat i := by
  ext a b
  rw [emb_Ai_apply, T9mat_formula]

private theorem Ai_prod : Ai 0 * Ai 1 * Ai 2 =
    Matrix.diagonal (fun _ => AdjoinRoot.root j9poly) := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [Ai, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal]

private noncomputable def Aroot : Matrix (Fin 3) (Fin 3) F8 :=
  Matrix.diagonal (fun _ : Fin 3 => AdjoinRoot.root j9poly)

private theorem T9_prod_val : (T9 0 * T9 1 * T9 2 : SL 9).1 = emb Aroot := by
  change T9mat 0 * T9mat 1 * T9mat 2 = emb Aroot
  rw [← emb_Ai 0, ← emb_Ai 1, ← emb_Ai 2, ← map_mul, ← map_mul]
  congr 1
  simpa [Aroot] using Ai_prod

private theorem emb_injective : Function.Injective emb := by
  intro A B h
  have h1 : (Matrix.compRingEquiv (Fin 3) (Fin 3) F2) (A.map reg) =
      (Matrix.compRingEquiv (Fin 3) (Fin 3) F2) (B.map reg) :=
    (Matrix.reindexRingEquiv F2 e9).injective h
  have h4 : A.map reg = B.map reg :=
    (Matrix.compRingEquiv (Fin 3) (Fin 3) F2).injective h1
  ext i j
  exact reg_injective (by
    have := congrFun (congrFun h4 i) j
    simpa [Matrix.map_apply] using this)

private noncomputable def E :
    Matrix (Fin 9) (Fin 9) F2 ≃+* Matrix (Fin 3) (Fin 3) (Matrix (Fin 3) (Fin 3) F2) :=
  (Matrix.reindexRingEquiv F2 e9).symm.trans (Matrix.compRingEquiv (Fin 3) (Fin 3) F2).symm

private theorem E_emb (A : Matrix (Fin 3) (Fin 3) F8) : E (emb A) = A.map reg := by
  change (Matrix.compRingEquiv (Fin 3) (Fin 3) F2).symm
    ((Matrix.reindexRingEquiv F2 e9).symm
      ((Matrix.reindexRingEquiv F2 e9)
        ((Matrix.compRingEquiv (Fin 3) (Fin 3) F2) (A.map reg)))) = A.map reg
  rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]

private theorem Aroot_map_reg : Aroot.map reg = Matrix.diagonal (fun _ : Fin 3 => Om) := by
  unfold Aroot
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;> simp [Matrix.diagonal, h, reg_root]

private theorem diag_mul_comm (X : Matrix (Fin 3) (Fin 3) (Matrix (Fin 3) (Fin 3) F2))
    (h : X * Matrix.diagonal (fun _ => Om) = Matrix.diagonal (fun _ => Om) * X) :
    ∀ i j, X i j * Om = Om * X i j := by
  intro i j
  have := congrFun (congrFun h i) j
  simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal] using this

private theorem emb_one_apply (a b : Fin 9) :
    emb (1 : Matrix (Fin 3) (Fin 3) F8) a b = (if a = b then 1 else 0) := by
  rw [map_one, Matrix.one_apply]

private theorem emb_single_apply (i j : Fin 3) (c : F8) (a b : Fin 9) :
    emb (Matrix.single i j c) a b =
      (if bIdx9 a = i ∧ bIdx9 b = j then reg c (iIdx9 a) (iIdx9 b) else 0) := by
  rw [emb_apply, Matrix.single_apply]
  by_cases h1 : bIdx9 a = i <;> by_cases h2 : bIdx9 b = j <;>
    simp_all [eq_comm, map_zero]

private theorem emb_transvection (i j : Fin 3) (hij : i ≠ j) (c : F8) (a b : Fin 9) :
    emb (1 + Matrix.single i j c) a b =
      (if a = b then 1 else 0) +
        (if bIdx9 a = i ∧ bIdx9 b = j then reg c (iIdx9 a) (iIdx9 b) else 0) := by
  rw [map_add, Matrix.add_apply, emb_one_apply, emb_single_apply]

private theorem F2_units_eq_one (u : F2ˣ) : u = 1 := by
  have h : (u : F2) ≠ 0 := u.ne_zero
  rcases F2_eq_zero_or_one (u : F2) with h0 | h1
  · exact absurd h0 h
  · exact Units.ext h1

private theorem emb_det_one (A : (Matrix (Fin 3) (Fin 3) F8)ˣ) :
    (emb (A : Matrix (Fin 3) (Fin 3) F8)).det = 1 := by
  have h := F2_units_eq_one (Matrix.GeneralLinearGroup.det (Units.map emb.toMonoidHom A))
  have h' := congrArg (fun u : F2ˣ => (u : F2)) h
  rw [Matrix.GeneralLinearGroup.val_det_apply] at h'
  simpa [Units.coe_map] using h'

private noncomputable def embSL : (Matrix (Fin 3) (Fin 3) F8)ˣ →* SL 9 where
  toFun A := ⟨emb (A : Matrix (Fin 3) (Fin 3) F8), emb_det_one A⟩
  map_one' := by
    apply Subtype.ext
    show emb ((1 : (Matrix (Fin 3) (Fin 3) F8)ˣ) : Matrix (Fin 3) (Fin 3) F8) =
      (1 : Matrix (Fin 9) (Fin 9) F2)
    rw [Units.val_one, map_one]
  map_mul' := by
    intro A B
    apply Subtype.ext
    change emb ((A * B : (Matrix (Fin 3) (Fin 3) F8)ˣ) : Matrix (Fin 3) (Fin 3) F8) =
      emb (A : Matrix (Fin 3) (Fin 3) F8) * emb (B : Matrix (Fin 3) (Fin 3) F8)
    rw [Units.val_mul, map_mul]

private noncomputable def ArootInv : Matrix (Fin 3) (Fin 3) F8 :=
  Matrix.diagonal (fun _ : Fin 3 => (AdjoinRoot.root j9poly)⁻¹)

private theorem root_ne_zero : AdjoinRoot.root j9poly ≠ 0 := by
  intro h
  have : Om = 0 := by rw [← reg_root, h, map_zero]
  have h2 := congrFun (congrFun this 0) 2
  simp [Om] at h2

private theorem Aroot_mul_inv : Aroot * ArootInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Aroot, ArootInv, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal,
      mul_inv_cancel₀ root_ne_zero]

private theorem Aroot_inv_mul : ArootInv * Aroot = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Aroot, ArootInv, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal,
      inv_mul_cancel₀ root_ne_zero]

private noncomputable def ArootUnit : (Matrix (Fin 3) (Fin 3) F8)ˣ where
  val := Aroot
  inv := ArootInv
  val_inv := Aroot_mul_inv
  inv_val := Aroot_inv_mul

private theorem T9_prod_eq : (T9 0 * T9 1 * T9 2 : SL 9) = embSL ArootUnit := by
  apply Subtype.ext
  rw [T9_prod_val]
  rfl

private theorem embSL_range_le_centralizer :
    embSL.range ≤ Subgroup.centralizer ({T9 0 * T9 1 * T9 2} : Set (SL 9)) := by
  rintro g ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [T9_prod_eq, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  simp only [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ArootUnit, Aroot, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal, mul_comm]

private theorem isUnit_of_emb_isUnit (A : Matrix (Fin 3) (Fin 3) F8) (h : IsUnit (emb A)) :
    IsUnit A := by
  have hinj : Function.Injective (fun B : Matrix (Fin 3) (Fin 3) F8 => A * B) := by
    intro B C hBC
    have hBC' : A * B = A * C := hBC
    have h1 : emb A * emb B = emb A * emb C := by
      rw [← map_mul, ← map_mul, hBC']
    exact emb_injective (h.mul_left_cancel h1)
  obtain ⟨B, hB⟩ := Finite.surjective_of_injective hinj 1
  exact IsUnit.of_mul_eq_one B hB

private theorem centralizer_le_embSL_range :
    Subgroup.centralizer ({T9 0 * T9 1 * T9 2} : Set (SL 9)) ≤ embSL.range := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hg' : g.1 * emb Aroot = emb Aroot * g.1 := by
    have h := congrArg Subtype.val hg
    rw [Matrix.SpecialLinearGroup.coe_mul (A := g) (B := T9 0 * T9 1 * T9 2),
      Matrix.SpecialLinearGroup.coe_mul (A := T9 0 * T9 1 * T9 2) (B := g)] at h
    simpa only [T9_prod_val] using h
  have hcomm : E g.1 * Matrix.diagonal (fun _ : Fin 3 => Om) =
      Matrix.diagonal (fun _ : Fin 3 => Om) * E g.1 := by
    have h := congrArg E hg'
    rw [map_mul, map_mul, E_emb, Aroot_map_reg] at h
    exact h
  have hblk : ∀ i j, E g.1 i j * Om = Om * E g.1 i j :=
    diag_mul_comm (E g.1) hcomm
  let A : Matrix (Fin 3) (Fin 3) F8 := fun i j =>
    Classical.choose (RingHom.mem_range.mp (reg_surj (E g.1 i j) (hblk i j)))
  have hA : ∀ i j, reg (A i j) = E g.1 i j := fun i j =>
    Classical.choose_spec (RingHom.mem_range.mp (reg_surj (E g.1 i j) (hblk i j)))
  have hA' : A.map reg = E g.1 := by
    ext i j
    rw [Matrix.map_apply, hA]
  have hEA : emb A = g.1 := by
    apply E.injective
    rw [E_emb, hA']
  have hunit : IsUnit A := by
    apply isUnit_of_emb_isUnit
    rw [hEA]
    exact IsUnit.of_mul_eq_one (g⁻¹).1 (by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one])
  rw [MonoidHom.mem_range]
  refine ⟨hunit.unit, ?_⟩
  apply Subtype.ext
  show emb (hunit.unit : Matrix (Fin 3) (Fin 3) F8) = g.1
  rw [IsUnit.unit_spec]
  exact hEA

private theorem centralizer_eq_embSL_range :
    Subgroup.centralizer ({T9 0 * T9 1 * T9 2} : Set (SL 9)) = embSL.range :=
  le_antisymm centralizer_le_embSL_range embSL_range_le_centralizer

private noncomputable def psi : Matrix.SpecialLinearGroup (Fin 3) F8 →* SL 9 :=
  embSL.comp (Matrix.SpecialLinearGroup.toGL (n := Fin 3) (R := F8))

private theorem psi_transvection_mem (t : TransvectionStruct (Fin 3) F8) :
    psi t.toSpecialLinearGroup ∈ GJ := by
  apply Subgroup.subset_closure
  refine ⟨t.i, t.j, t.hij, ?_⟩
  refine ⟨reg t.c, reg_comm t.c, ?_⟩
  intro a b
  have hval : (psi t.toSpecialLinearGroup).1 = emb (1 + Matrix.single t.i t.j t.c) := by
    have h1 : (↑(Matrix.SpecialLinearGroup.toGL t.toSpecialLinearGroup) :
        Matrix (Fin 3) (Fin 3) F8) = Matrix.transvection t.i t.j t.c := by
      change (↑t.toSpecialLinearGroup : Matrix (Fin 3) (Fin 3) F8) =
        Matrix.transvection t.i t.j t.c
      rw [TransvectionStruct.toSpecialLinearGroup_coe]
      rfl
    show emb (↑(Matrix.SpecialLinearGroup.toGL t.toSpecialLinearGroup) :
      Matrix (Fin 3) (Fin 3) F8) = _
    rw [h1]
    rfl
  rw [hval, emb_transvection t.i t.j t.hij t.c a b]
  simp only [blk_castLE, idxIn_castLE, Fin.castSucc_inj]

private theorem psi_range_le_GJ : psi.range ≤ GJ := by
  rw [MonoidHom.range_eq_map,
    ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin 3) (K := F8),
    MonoidHom.map_closure]
  rw [Subgroup.closure_le]
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨t, rfl⟩ := hs
  exact psi_transvection_mem t

private theorem commutator_le_psi_range :
    ⁅Subgroup.centralizer ({T9 0 * T9 1 * T9 2} : Set (SL 9)),
      Subgroup.centralizer ({T9 0 * T9 1 * T9 2} : Set (SL 9))⁆ ≤ psi.range := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [centralizer_eq_embSL_range] at ha hb
  obtain ⟨A, rfl⟩ := ha
  obtain ⟨B, rfl⟩ := hb
  have hdetu : Matrix.GeneralLinearGroup.det (A * B * A⁻¹ * B⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hdet : ((A * B * A⁻¹ * B⁻¹ : (Matrix (Fin 3) (Fin 3) F8)ˣ) :
      Matrix (Fin 3) (Fin 3) F8).det = 1 := by
    have := congrArg (fun u : F8ˣ => (u : F8)) hdetu
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  rw [MonoidHom.mem_range]
  refine ⟨⟨(A * B * A⁻¹ * B⁻¹ : (Matrix (Fin 3) (Fin 3) F8)ˣ), hdet⟩, ?_⟩
  show embSL (A * B * A⁻¹ * B⁻¹) =
    embSL A * embSL B * (embSL A)⁻¹ * (embSL B)⁻¹
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]

theorem a11J9GenInput_holds : J9 ≤ GJ := by
  unfold J9
  exact le_trans commutator_le_psi_range psi_range_le_GJ

end CFSG.StandardType.A11

end

module

public import CFSG.Timmesfeld.RankTwo.SimplyLaced
public import CFSG.LieType.Steinberg.Classical.SpecialLinear

public section

namespace CFSG.Timmesfeld.ARS

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.RootSystem

namespace Linear

section Block

variable (F : Type*) [Field F] {k n : ℕ} (e : Fin k ↪ Fin n)

open Classical in
noncomputable def embEquiv : Fin k ⊕ {a : Fin n // a ∉ Set.range e} ≃ Fin n :=
  (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
    (Equiv.sumCompl fun a => a ∈ Set.range e)

omit [Field F] in
@[simp] theorem embEquiv_inl (p : Fin k) : embEquiv e (Sum.inl p) = e p := by
  simp [embEquiv]

omit [Field F] in
@[simp] theorem embEquiv_inr (a : {a : Fin n // a ∉ Set.range e}) :
    embEquiv e (Sum.inr a) = a := by
  simp [embEquiv]

noncomputable def blockMat (A : Matrix (Fin k) (Fin k) F) : Matrix (Fin n) (Fin n) F :=
  Matrix.reindexAlgEquiv F F (embEquiv e) (Matrix.fromBlocks A 0 0 1)

theorem blockMat_apply (A : Matrix (Fin k) (Fin k) F) (p q) :
    blockMat F e A (embEquiv e p) (embEquiv e q) = Matrix.fromBlocks A 0 0 1 p q := by
  simp [blockMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]

theorem blockMat_mul (A B : Matrix (Fin k) (Fin k) F) :
    blockMat F e (A * B) = blockMat F e A * blockMat F e B := by
  rw [blockMat, blockMat, blockMat, ← map_mul, Matrix.fromBlocks_multiply]
  simp

theorem blockMat_one : blockMat F e (1 : Matrix (Fin k) (Fin k) F) = 1 := by
  rw [blockMat, Matrix.fromBlocks_one, map_one]

theorem det_blockMat (A : Matrix (Fin k) (Fin k) F) : (blockMat F e A).det = A.det := by
  rw [blockMat, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem blockMat_injective : Function.Injective (blockMat F e) := fun A B h => by
  have h' := (Matrix.reindexAlgEquiv F F (embEquiv e)).injective h
  exact (Matrix.fromBlocks_inj.1 h').1

omit [Field F] in
theorem ext_embEquiv {R : Type*} {M N : Matrix (Fin n) (Fin n) R}
    (h : ∀ p q, M (embEquiv e p) (embEquiv e q) = N (embEquiv e p) (embEquiv e q)) : M = N := by
  ext a b
  obtain ⟨p, rfl⟩ := (embEquiv e).surjective a
  obtain ⟨q, rfl⟩ := (embEquiv e).surjective b
  exact h p q

theorem blockMat_transvection {p q : Fin k} (c : F) :
    blockMat F e (transvection p q c) = transvection (e p) (e q) c := by
  refine ext_embEquiv e fun x y => ?_
  rw [blockMat_apply]
  rcases x with x | ⟨a, ha⟩ <;> rcases y with y | ⟨b, hb⟩
  · simp [transvection, Matrix.one_apply, Matrix.single_apply, e.injective.eq_iff]
  · have hb' : ∀ r, e r ≠ b := fun r h => hb ⟨r, h⟩
    simp [transvection, hb' x, hb' q]
  · have ha' : ∀ r, e r ≠ a := fun r h => ha ⟨r, h⟩
    simp [transvection, Ne.symm (ha' y), ha' p]
  · have ha' : ∀ r, e r ≠ a := fun r h => ha ⟨r, h⟩
    simp [transvection, Matrix.one_apply, Matrix.fromBlocks_apply₂₂, Subtype.ext_iff, ha' p]

noncomputable def blockHom : SpecialLinearGroup (Fin k) F →* SpecialLinearGroup (Fin n) F where
  toFun A := ⟨blockMat F e (A : Matrix (Fin k) (Fin k) F), by rw [det_blockMat]; exact A.2⟩
  map_one' := Subtype.ext (by
    change blockMat F e ((1 : Matrix.SpecialLinearGroup (Fin k) F) : Matrix (Fin k) (Fin k) F) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, blockMat_one])
  map_mul' A B := Subtype.ext (by
    change blockMat F e ((A * B : Matrix.SpecialLinearGroup (Fin k) F) :
        Matrix (Fin k) (Fin k) F) =
      blockMat F e (A : Matrix (Fin k) (Fin k) F) * blockMat F e (B : Matrix (Fin k) (Fin k) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, blockMat_mul])

theorem blockHom_injective : Function.Injective (blockHom F e) := fun _ _ h =>
  Subtype.ext (blockMat_injective F e (congrArg Subtype.val h))

theorem blockHom_tv {p q : Fin k} (hpq : p ≠ q) (c : F) :
    blockHom F e (tv p q c) = tv (e p) (e q) c := by
  rw [tv_of_ne hpq, tv_of_ne (e.injective.ne hpq)]
  exact Subtype.ext (blockMat_transvection F e c)

end Block

section Diag

variable (F : Type*) [Field F]

noncomputable def diagMat (A B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F :=
  Matrix.reindexAlgEquiv F F finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

theorem det_diagMat (A B : Matrix (Fin 2) (Fin 2) F) : (diagMat F A B).det = A.det * B.det := by
  rw [diagMat, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁]

noncomputable def diagHom :
    SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F →*
      SpecialLinearGroup (Fin (2 + 2)) F
    where
  toFun A := ⟨diagMat F (A.1 : Matrix (Fin 2) (Fin 2) F) (A.2 : Matrix (Fin 2) (Fin 2) F), by
    rw [det_diagMat, A.1.2, A.2.2, mul_one]⟩
  map_one' := Subtype.ext (by
    change diagMat F ((1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      ((1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, diagMat, Matrix.fromBlocks_one, map_one])
  map_mul' A B := Subtype.ext (by
    change diagMat F ((A.1 * B.1 : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)
        ((A.2 * B.2 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      diagMat F (A.1 : Matrix (Fin 2) (Fin 2) F) (A.2 : Matrix (Fin 2) (Fin 2) F) *
        diagMat F (B.1 : Matrix (Fin 2) (Fin 2) F) (B.2 : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, diagMat, diagMat,
      diagMat, ← map_mul, Matrix.fromBlocks_multiply]
    simp)

theorem diagHom_injective : Function.Injective (diagHom F) := by
  rintro ⟨A, B⟩ ⟨A', B'⟩ h
  have h' := (Matrix.reindexAlgEquiv F F finSumFinEquiv).injective (congrArg Subtype.val h)
  obtain ⟨h1, -, -, h4⟩ := Matrix.fromBlocks_inj.1 h'
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h4)

theorem diagHom_tv_left {p q : Fin 2} (hpq : p ≠ q) (c : F) :
    diagHom F (tv p q c, 1) = tv (Fin.castAdd 2 p) (Fin.castAdd 2 q) c := by
  rw [tv_of_ne hpq, tv_of_ne fun h => hpq (Fin.castAdd_injective 2 2 h)]
  refine Subtype.ext ?_
  change diagMat F (transvection p q c) 1 = transvection _ _ c
  ext a b
  induction a using Fin.addCases <;> induction b using Fin.addCases <;> rename_i x y <;>
    simp only [diagMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂] <;>
    fin_cases p <;> fin_cases q <;> fin_cases x <;> fin_cases y <;>
    simp_all [transvection, Fin.ext_iff]

theorem diagHom_tv_right {p q : Fin 2} (hpq : p ≠ q) (c : F) :
    diagHom F (1, tv p q c) = tv (Fin.natAdd 2 p) (Fin.natAdd 2 q) c := by
  rw [tv_of_ne hpq, tv_of_ne fun h => hpq (Fin.natAdd_injective 2 2 h)]
  refine Subtype.ext ?_
  change diagMat F 1 (transvection p q c) = transvection _ _ c
  ext a b
  induction a using Fin.addCases <;> induction b using Fin.addCases <;> rename_i x y <;>
    simp only [diagMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂] <;>
    fin_cases p <;> fin_cases q <;> fin_cases x <;> fin_cases y <;>
    simp_all [transvection, Fin.ext_iff]

end Diag

section Roots

variable {m : ℕ}

theorem eq_smul_sroot_add {i j : Fin m} (hij : i ≠ j) {γ : Fin m → ℤ}
    (h : ∀ k, k ≠ i → k ≠ j → γ k = 0) : γ = γ i • sroot i + γ j • sroot j := by
  funext k
  by_cases hki : k = i
  · subst hki
    simp [sroot, hij]
  by_cases hkj : k = j
  · subst hkj
    simp [sroot, hki]
  · simp [sroot, hki, hkj, h k hki hkj]

theorem eq_smul_sroot {i : Fin m} {γ : Fin m → ℤ} (h : ∀ k, k ≠ i → γ k = 0) :
    γ = γ i • sroot i := by
  funext k
  by_cases hki : k = i
  · subst hki
    simp [sroot]
  · simp [sroot, hki, h k hki]

theorem single_sub_single_apply {n : ℕ} {a b : Fin n} (hab : a ≠ b) (p : Fin n) :
    ((Pi.single a 1 - Pi.single b 1 : Fin n → ℤ) p = 0 ∧ p ≠ a ∧ p ≠ b) ∨
      ((Pi.single a 1 - Pi.single b 1 : Fin n → ℤ) p = 1 ∧ p = a) ∨
      ((Pi.single a 1 - Pi.single b 1 : Fin n → ℤ) p = -1 ∧ p = b) := by
  by_cases hpa : p = a
  · subst hpa
    simp [hab]
  by_cases hpb : p = b
  · subst hpb
    simp [Ne.symm hab]
  · simp [hpa, hpb]

theorem toStd_smul_sroot_add (c d : ℤ) (i j : Fin m) :
    toStd m (c • sroot i + d • sroot j) =
      c • (Pi.single i.castSucc 1 - Pi.single i.succ 1) +
        d • (Pi.single j.castSucc 1 - Pi.single j.succ 1) := by
  rw [CFSG.LieType.Steinberg.SL.toStd_add, toStd_smul, toStd_smul, toStd_single, toStd_single]

theorem mem_of_mem_pairRoots_adj (F : Type) [Field F] {i j : Fin m} (hij : j.val = i.val + 1)
    {γ : Fin m → ℤ} (hγ : γ ∈ pairRoots (SpecialLinear.rootDatum m F) i j) :
    γ ∈ ({sroot i, -sroot i, sroot j, -sroot j, sroot i + sroot j, -(sroot i + sroot j)} :
      Set (Fin m → ℤ)) := by
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  obtain ⟨hroot, hsupp⟩ := hγ
  have hroot' : γ ∈ roots (isFiniteType_A m) ∅ := hroot
  rw [roots_eq] at hroot'
  obtain ⟨a, b, hab, hst⟩ := hroot'
  have hdec := eq_smul_sroot_add hne hsupp
  rw [hdec, toStd_smul_sroot_add] at hst
  have hjcs : j.castSucc = i.succ := Fin.ext (by simp [hij])
  have h1 : i.castSucc ≠ i.succ := Fin.castSucc_lt_succ.ne
  have h2 : i.castSucc ≠ j.succ := fun h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have h3 : i.succ ≠ j.succ := fun h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have e0 : (Pi.single a 1 - Pi.single b 1 : Fin (m + 1) → ℤ) i.castSucc = γ i := by
    rw [← hst]
    simp [hjcs, h1, h2]
  have e1 : (Pi.single a 1 - Pi.single b 1 : Fin (m + 1) → ℤ) i.succ = γ j - γ i := by
    rw [← hst]
    simp [hjcs, Ne.symm h1, h3]
    ring
  have e2 : (Pi.single a 1 - Pi.single b 1 : Fin (m + 1) → ℤ) j.succ = -γ j := by
    rw [← hst]
    simp [hjcs, Ne.symm h2, Ne.symm h3]
  have r0 := single_sub_single_apply hab i.castSucc
  have r1 := single_sub_single_apply hab i.succ
  have r2 := single_sub_single_apply hab j.succ
  rw [e0] at r0
  rw [e1] at r1
  rw [e2] at r2
  have hγ0 : γ i ≠ 0 ∨ γ j ≠ 0 := by
    by_contra! h0
    rw [h0.1, h0.2] at hst
    simp only [zero_smul, add_zero] at hst
    have := congrFun hst a
    simp [hab] at this
  have key : (γ i = 1 ∧ γ j = 0) ∨ (γ i = -1 ∧ γ j = 0) ∨ (γ i = 0 ∧ γ j = 1) ∨
      (γ i = 0 ∧ γ j = -1) ∨ (γ i = 1 ∧ γ j = 1) ∨ (γ i = -1 ∧ γ j = -1) := by
    rcases r0 with ⟨r0, -⟩ | ⟨r0, -⟩ | ⟨r0, -⟩ <;> rcases r1 with ⟨r1, -⟩ | ⟨r1, -⟩ | ⟨r1, -⟩ <;>
      rcases r2 with ⟨r2, -⟩ | ⟨r2, -⟩ | ⟨r2, -⟩ <;> omega
  rw [hdec]
  rcases key with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ <;>
    rw [hi, hj]
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inr (Or.inr (Or.inl (by simp)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [Set.mem_singleton_iff]; abel)))))

theorem single_sub_single_apply_val {n : ℕ} {a b : Fin n} (hab : a ≠ b) (p : Fin n) {v : ℤ}
    (hv : (Pi.single a 1 - Pi.single b 1 : Fin n → ℤ) p = v) :
    v = 0 ∨ (v = 1 ∧ p.val = a.val) ∨ (v = -1 ∧ p.val = b.val) := by
  rcases single_sub_single_apply hab p with ⟨h, -⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩
  · exact Or.inl (hv ▸ h)
  · exact Or.inr (Or.inl ⟨hv ▸ h, rfl⟩)
  · exact Or.inr (Or.inr ⟨hv ▸ h, rfl⟩)

theorem mem_of_mem_pairRoots_nonadj (F : Type) [Field F] {i j : Fin m}
    (h1 : ¬ j.val = i.val + 1) (h2 : ¬ i.val = j.val + 1) {γ : Fin m → ℤ}
    (hγ : γ ∈ pairRoots (SpecialLinear.rootDatum m F) i j) :
    γ ∈ ({sroot i, -sroot i, sroot j, -sroot j} : Set (Fin m → ℤ)) := by
  obtain ⟨hroot, hsupp⟩ := hγ
  have hroot' : γ ∈ roots (isFiniteType_A m) ∅ := hroot
  rw [roots_eq] at hroot'
  obtain ⟨a, b, hab, hst⟩ := hroot'
  have hnz : ∀ k, γ k ≠ 0 → k = i ∨ k = j := fun k hk => by
    by_contra! h
    exact hk (hsupp k h.1 h.2)
  by_cases hij : i = j
  · subst hij
    have hdec := eq_smul_sroot (m := m) (i := i) fun k hk => hsupp k hk hk
    have hst' := hst
    rw [hdec, toStd_smul, toStd_single] at hst'
    have e0 : (Pi.single a 1 - Pi.single b 1 : Fin (m + 1) → ℤ) i.castSucc = γ i := by
      rw [← hst']
      simp [Fin.castSucc_lt_succ.ne]
    have hγ0 : γ i ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hst'
      have := congrFun hst' a
      simp [hab] at this
    rcases single_sub_single_apply_val hab i.castSucc e0 with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hγ0
    · rw [hdec, h]
      exact Or.inl (by simp)
    · rw [hdec, h]
      exact Or.inr (Or.inl (by simp))
  · have hdec := eq_smul_sroot_add hij hsupp
    have hst' := hst
    rw [hdec, toStd_smul_sroot_add] at hst'
    have hv : ∀ x y : Fin (m + 1), x.val = y.val → x = y := fun x y h => Fin.ext h
    have hiv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have q1 : i.castSucc ≠ i.succ := Fin.castSucc_lt_succ.ne
    have q2 : i.castSucc ≠ j.castSucc := fun h => hiv (by simpa using congrArg Fin.val h)
    have q3 : i.castSucc ≠ j.succ := fun h => h2 (by simpa using congrArg Fin.val h)
    have q4 : i.succ ≠ j.castSucc := fun h => h1 (by simpa using (congrArg Fin.val h).symm)
    have q5 : i.succ ≠ j.succ := fun h => hiv (by simpa using congrArg Fin.val h)
    have q6 : j.castSucc ≠ j.succ := Fin.castSucc_lt_succ.ne
    have e0 : (Pi.single a 1 - Pi.single b 1 : Fin (m + 1) → ℤ) i.castSucc = γ i := by
      rw [← hst']
      simp [q1, q2, q3]
    have e1 : (Pi.single a 1 - Pi.single b 1 : Fin (m + 1) → ℤ) i.succ = -γ i := by
      rw [← hst']
      simp [Ne.symm q1, q4, q5]
    have e2 : (Pi.single a 1 - Pi.single b 1 : Fin (m + 1) → ℤ) j.castSucc = γ j := by
      rw [← hst']
      simp [Ne.symm q2, Ne.symm q4, q6]
    have e3 : (Pi.single a 1 - Pi.single b 1 : Fin (m + 1) → ℤ) j.succ = -γ j := by
      rw [← hst']
      simp [Ne.symm q3, Ne.symm q5, Ne.symm q6]
    have r0 := single_sub_single_apply_val hab _ e0
    have r1 := single_sub_single_apply_val hab _ e1
    have r2 := single_sub_single_apply_val hab _ e2
    have r3 := single_sub_single_apply_val hab _ e3
    simp only [Fin.val_castSucc, Fin.val_succ] at r0 r1 r2 r3
    have hγ0 : γ i ≠ 0 ∨ γ j ≠ 0 := by
      by_contra! h0
      rw [h0.1, h0.2] at hst'
      simp only [zero_smul, add_zero] at hst'
      have := congrFun hst' a
      simp [hab] at this
    have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    have key : (γ i = 1 ∧ γ j = 0) ∨ (γ i = -1 ∧ γ j = 0) ∨ (γ i = 0 ∧ γ j = 1) ∨
        (γ i = 0 ∧ γ j = -1) := by
      omega
    rw [hdec]
    rcases key with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> rw [hi, hj]
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl (by simp))
    · exact Or.inr (Or.inr (Or.inl (by simp)))
    · exact Or.inr (Or.inr (Or.inr (by simp)))

end Roots

section Param

variable {m : ℕ} {F : Type} [Field F]

open CFSG.LieType.Steinberg.SL in
theorem x_sroot (k : Fin m) (c : F) : x m F (sroot k) c = tv k.castSucc k.succ c := by
  rw [x_eq Fin.castSucc_lt_succ.ne (toStd_single m k), tv_of_ne]

open CFSG.LieType.Steinberg.SL in
theorem x_neg_sroot (k : Fin m) (c : F) : x m F (-sroot k) c = tv k.succ k.castSucc c := by
  rw [x_eq Fin.castSucc_lt_succ.ne' (by rw [toStd_neg, toStd_single, neg_sub]), tv_of_ne]

theorem castSucc_eq_succ_of_val {i j : Fin m} (hij : j.val = i.val + 1) :
    j.castSucc = i.succ :=
  Fin.ext (by simp [hij])

theorem castSucc_ne_succ_of_val {i j : Fin m} (hij : j.val = i.val + 1) :
    i.castSucc ≠ j.succ := fun h => by
  have := congrArg Fin.val h
  simp at this
  omega

open CFSG.LieType.Steinberg.SL in
theorem x_sroot_add {i j : Fin m} (hij : j.val = i.val + 1) (c : F) :
    x m F (sroot i + sroot j) c = tv i.castSucc j.succ c := by
  rw [x_eq (castSucc_ne_succ_of_val hij) (by
    rw [toStd_add, toStd_single, toStd_single, castSucc_eq_succ_of_val hij]; abel), tv_of_ne]

open CFSG.LieType.Steinberg.SL in
theorem x_neg_sroot_add {i j : Fin m} (hij : j.val = i.val + 1) (c : F) :
    x m F (-(sroot i + sroot j)) c = tv j.succ i.castSucc c := by
  rw [x_eq (castSucc_ne_succ_of_val hij).symm (by
    rw [toStd_neg, toStd_add, toStd_single, toStd_single, castSucc_eq_succ_of_val hij]; abel),
    tv_of_ne]

end Param

end Linear

section Instance

open Linear CFSG.LieType.Steinberg.SL

variable (m : ℕ) (F : Type) [Field F]

theorem simplyLacedLevis_specialLinear :
    SimplyLacedLevis (SpecialLinear.rootDatum m F) F (fun i j => j.val = i.val + 1) (x m F) where
  asymm i j h h' := by omega
  ne i j h e := by subst e; omega
  mem γ hγ c := ((isParametrization (m := m) (F := F) γ hγ).1 _).2 ⟨c, rfl⟩
  surj γ hγ g hg := ((isParametrization (m := m) (F := F) γ hγ).1 g).1 hg
  pairRoots_adj i j h γ hγ := mem_of_mem_pairRoots_adj F h hγ
  pairRoots_nonadj i j h h' γ hγ := mem_of_mem_pairRoots_nonadj F h h' hγ
  sl3 i j h := by
    change Fin m at i j
    let e : Fin 3 ↪ Fin (m + 1) := ⟨![i.castSucc, i.succ, j.succ], by
      intro a b hab
      have := congrArg Fin.val hab
      fin_cases a <;> fin_cases b <;> simp at this ⊢ <;> omega⟩
    refine ⟨blockHom F e, blockHom_injective F e, fun c => ?_⟩
    have he0 : e 0 = i.castSucc := rfl
    have he1 : e 1 = i.succ := rfl
    have he2 : e 2 = j.succ := rfl
    rw [blockHom_tv F e (by decide), blockHom_tv F e (by decide), blockHom_tv F e (by decide),
      blockHom_tv F e (by decide), blockHom_tv F e (by decide), blockHom_tv F e (by decide),
      he0, he1, he2]
    have hj : j.castSucc = i.succ := castSucc_eq_succ_of_val (m := m) h
    exact ⟨(x_sroot i c).symm, (x_neg_sroot i c).symm,
      ((x_sroot j c).trans (by rw [hj])).symm, ((x_neg_sroot j c).trans (by rw [hj])).symm,
      (x_sroot_add (m := m) h c).symm, (x_neg_sroot_add (m := m) h c).symm⟩
  sl2 k := by
    change Fin m at k
    let e : Fin 2 ↪ Fin (m + 1) := ⟨![k.castSucc, k.succ], by
      intro a b hab
      have := congrArg Fin.val hab
      fin_cases a <;> fin_cases b <;> simp at this ⊢⟩
    refine ⟨blockHom F e, blockHom_injective F e, fun c => ?_⟩
    rw [blockHom_tv F e (by decide), blockHom_tv F e (by decide)]
    exact ⟨(x_sroot k c).symm, (x_neg_sroot k c).symm⟩
  sl2sl2 i j hij h h' := by
    change Fin m at i j
    have hiv : i.val ≠ j.val := fun e => hij (Fin.ext e)
    let e : Fin (2 + 2) ↪ Fin (m + 1) := ⟨![i.castSucc, i.succ, j.castSucc, j.succ], by
      intro a b hab
      have := congrArg Fin.val hab
      fin_cases a <;> fin_cases b <;> simp at this ⊢ <;> omega⟩
    refine ⟨(blockHom F e).comp (diagHom F),
      (blockHom_injective F e).comp (diagHom_injective F), fun c => ?_⟩
    simp only [MonoidHom.comp_apply]
    have he0 : e (Fin.castAdd 2 0) = i.castSucc := rfl
    have he1 : e (Fin.castAdd 2 1) = i.succ := rfl
    have he2 : e (Fin.natAdd 2 0) = j.castSucc := rfl
    have he3 : e (Fin.natAdd 2 1) = j.succ := rfl
    rw [diagHom_tv_left F (by decide), diagHom_tv_left F (by decide),
      diagHom_tv_right F (by decide), diagHom_tv_right F (by decide), blockHom_tv F e (by decide),
      blockHom_tv F e (by decide), blockHom_tv F e (by decide), blockHom_tv F e (by decide), he0,
      he1, he2, he3]
    exact ⟨(x_sroot i c).symm, (x_neg_sroot i c).symm, (x_sroot j c).symm,
      (x_neg_sroot j c).symm⟩

end Instance

end CFSG.Timmesfeld.ARS

module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismTransport

public section

namespace CFSG.LocalAnalysis.SteinbergCD

open Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K]

@[expose] def IsRadicalMatrix (A : Submodule K (Fin 3 → K)) (N : Matrix (Fin 3) (Fin 3) K) :
    Prop :=
  (∀ v, N *ᵥ v ∈ A) ∧ ∀ v ∈ A, N *ᵥ v = 0

theorem matrix_eq_zero_of_mulVec {M : Matrix (Fin 3) (Fin 3) K} (h : ∀ v, M *ᵥ v = 0) :
    M = 0 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rwa [mulVec_single_one] at this

section IsRadicalMatrix

variable {A : Submodule K (Fin 3 → K)} {N N' : Matrix (Fin 3) (Fin 3) K}

theorem IsRadicalMatrix.mul_eq_zero (hN : IsRadicalMatrix A N) (hN' : IsRadicalMatrix A N') :
    N * N' = 0 :=
  matrix_eq_zero_of_mulVec fun v => by
    rw [← mulVec_mulVec]
    exact hN.2 _ (hN'.1 v)

theorem IsRadicalMatrix.add (hN : IsRadicalMatrix A N) (hN' : IsRadicalMatrix A N') :
    IsRadicalMatrix A (N + N') :=
  ⟨fun v => by
    rw [add_mulVec]
    exact A.add_mem (hN.1 v) (hN'.1 v), fun v hv => by
    rw [add_mulVec, hN.2 v hv, hN'.2 v hv, add_zero]⟩

theorem IsRadicalMatrix.neg (hN : IsRadicalMatrix A N) : IsRadicalMatrix A (-N) :=
  ⟨fun v => by
    rw [neg_mulVec]
    exact A.neg_mem (hN.1 v), fun v hv => by rw [neg_mulVec, hN.2 v hv, neg_zero]⟩

theorem isRadicalMatrix_zero : IsRadicalMatrix A 0 :=
  ⟨fun v => by rw [zero_mulVec]; exact A.zero_mem, fun v _ => zero_mulVec v⟩

theorem IsRadicalMatrix.conj (hN : IsRadicalMatrix A N) {P P' : Matrix (Fin 3) (Fin 3) K}
    (hP : P' * P = 1) : IsRadicalMatrix (A.map (mulVecLin P)) (P * N * P') := by
  refine ⟨fun v => ⟨N *ᵥ (P' *ᵥ v), hN.1 _, ?_⟩, fun w hw => ?_⟩
  · rw [mulVecLin_apply, mulVec_mulVec, mulVec_mulVec]
  · obtain ⟨a, ha, rfl⟩ := hw
    rw [mulVecLin_apply, mulVec_mulVec, mul_assoc, mul_assoc, hP, mul_one, ← mulVec_mulVec,
      hN.2 a ha, mulVec_zero]

end IsRadicalMatrix

theorem coe_inv_sub_one {A : Submodule K (Fin 3 → K)} {g : SpecialLinearGroup (Fin 3) K}
    (hg : IsRadicalMatrix A ((g : Matrix (Fin 3) (Fin 3) K) - 1)) :
    ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1 =
      -((g : Matrix (Fin 3) (Fin 3) K) - 1) := by
  have hNN := hg.mul_eq_zero hg
  have h1 : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h2 : (g : Matrix (Fin 3) (Fin 3) K) * (1 - ((g : Matrix (Fin 3) (Fin 3) K) - 1)) = 1 := by
    calc (g : Matrix (Fin 3) (Fin 3) K) * (1 - ((g : Matrix (Fin 3) (Fin 3) K) - 1))
        = 1 - ((g : Matrix (Fin 3) (Fin 3) K) - 1) * ((g : Matrix (Fin 3) (Fin 3) K) - 1) := by
          noncomm_ring
      _ = 1 := by rw [hNN, sub_zero]
  have h3 : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 - ((g : Matrix (Fin 3) (Fin 3) K) - 1) := by
    calc ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        = ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((g : Matrix (Fin 3) (Fin 3) K) * (1 - ((g : Matrix (Fin 3) (Fin 3) K) - 1))) := by
          rw [h2, mul_one]
      _ = 1 - ((g : Matrix (Fin 3) (Fin 3) K) - 1) := by rw [← mul_assoc, h1, one_mul]
  rw [h3]
  abel

@[expose] def radical (A : Submodule K (Fin 3 → K)) : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {g | IsRadicalMatrix A ((g : Matrix (Fin 3) (Fin 3) K) - 1)}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_one, sub_self]
    exact isRadicalMatrix_zero
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul] at *
    have e : (g : Matrix (Fin 3) (Fin 3) K) * h - 1 =
        ((g : Matrix (Fin 3) (Fin 3) K) - 1) + ((h : Matrix (Fin 3) (Fin 3) K) - 1) +
          ((g : Matrix (Fin 3) (Fin 3) K) - 1) * ((h : Matrix (Fin 3) (Fin 3) K) - 1) := by
      noncomm_ring
    rw [e, hg.mul_eq_zero hh, add_zero]
    exact hg.add hh
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at *
    rw [coe_inv_sub_one hg]
    exact hg.neg

theorem mem_radical {A : Submodule K (Fin 3 → K)} {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ radical A ↔ IsRadicalMatrix A ((g : Matrix (Fin 3) (Fin 3) K) - 1) :=
  Iff.rfl

theorem radical_mul_comm {A : Submodule K (Fin 3 → K)} {g h : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ radical A) (hh : h ∈ radical A) : g * h = h * g := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have e1 : (g : Matrix (Fin 3) (Fin 3) K) * h =
      1 + ((g : Matrix (Fin 3) (Fin 3) K) - 1) + ((h : Matrix (Fin 3) (Fin 3) K) - 1) +
        ((g : Matrix (Fin 3) (Fin 3) K) - 1) * ((h : Matrix (Fin 3) (Fin 3) K) - 1) := by
    noncomm_ring
  have e2 : (h : Matrix (Fin 3) (Fin 3) K) * g =
      1 + ((h : Matrix (Fin 3) (Fin 3) K) - 1) + ((g : Matrix (Fin 3) (Fin 3) K) - 1) +
        ((h : Matrix (Fin 3) (Fin 3) K) - 1) * ((g : Matrix (Fin 3) (Fin 3) K) - 1) := by
    noncomm_ring
  rw [e1, e2, (mem_radical.1 hg).mul_eq_zero (mem_radical.1 hh),
    (mem_radical.1 hh).mul_eq_zero (mem_radical.1 hg)]
  abel

section CharTwo

variable [CharP K 2]

theorem one_add_mul_one_add {A : Submodule K (Fin 3 → K)} {N : Matrix (Fin 3) (Fin 3) K}
    (hN : IsRadicalMatrix A N) : (1 + N) * (1 + N) = 1 := by
  have e : (1 + N) * (1 + N) = 1 + (2 : K) • N + N * N := by
    rw [two_smul]
    noncomm_ring
  rw [e, hN.mul_eq_zero hN, CharTwo.two_eq_zero, zero_smul, add_zero, add_zero]

theorem radical_sq {A : Submodule K (Fin 3 → K)} {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ radical A) : g ^ 2 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, pow_two]
  have h := one_add_mul_one_add (mem_radical.1 hg)
  rwa [add_sub_cancel] at h

instance isElementaryAbelian_radical (A : Submodule K (Fin 3 → K)) :
    IsElementaryAbelian 2 (radical A) where
  is_comm := ⟨fun x y => Subtype.ext (radical_mul_comm x.2 y.2)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, radical_sq x.2, Subgroup.coe_one])

theorem det_one_add {A : Submodule K (Fin 3 → K)} {N : Matrix (Fin 3) (Fin 3) K}
    (hN : IsRadicalMatrix A N) : (1 + N).det = 1 := by
  have h := congrArg det (one_add_mul_one_add hN)
  rw [det_mul, det_one] at h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : ((1 + N).det - 1) * ((1 + N).det - 1) = 0 := by
    linear_combination h + (1 - (1 + N).det) * h2
  exact sub_eq_zero.1 (mul_self_eq_zero.1 h3)

theorem exists_mem_radical_iff {A : Submodule K (Fin 3 → K)} (M : Matrix (Fin 3) (Fin 3) K) :
    (∃ N, IsRadicalMatrix A N ∧ M = 1 + N) ↔
      ∃ g ∈ radical A, (g : Matrix (Fin 3) (Fin 3) K) = M := by
  constructor
  · rintro ⟨N, hN, rfl⟩
    refine ⟨(⟨1 + N, det_one_add hN⟩ : SpecialLinearGroup (Fin 3) K), ?_, rfl⟩
    show IsRadicalMatrix A (1 + N - 1)
    rwa [add_sub_cancel_left]
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, hg, (add_sub_cancel _ _).symm⟩

@[expose] noncomputable def radicalEquiv (A : Submodule K (Fin 3 → K)) :
    radical A ≃ {N : Matrix (Fin 3) (Fin 3) K // IsRadicalMatrix A N} where
  toFun g := ⟨((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1, g.2⟩
  invFun N := ⟨(⟨1 + N.1, det_one_add N.2⟩ : SpecialLinearGroup (Fin 3) K), by
    show IsRadicalMatrix A (1 + N.1 - 1)
    rw [add_sub_cancel_left]
    exact N.2⟩
  left_inv g := Subtype.ext (Subtype.ext (add_sub_cancel _ _))
  right_inv N := Subtype.ext (add_sub_cancel_left _ _)

end CharTwo

theorem conj_mem_radical {A : Submodule K (Fin 3 → K)} {x : SpecialLinearGroup (Fin 3) K}
    (hx : x ∈ radical A) (g : SpecialLinearGroup (Fin 3) K) :
    g * x * g⁻¹ ∈ radical (A.map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K))) := by
  rw [mem_radical]
  have hgg : (g : Matrix (Fin 3) (Fin 3) K) *
      ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have e : ((g * x * g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1 =
      (g : Matrix (Fin 3) (Fin 3) K) * ((x : Matrix (Fin 3) (Fin 3) K) - 1) *
        ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, mul_sub, sub_mul,
      mul_one, hgg]
  rw [e]
  exact (mem_radical.1 hx).conj (by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one])

theorem map_conj_radical (g : SpecialLinearGroup (Fin 3) K) (A : Submodule K (Fin 3 → K)) :
    (radical A).map (MulAut.conj g).toMonoidHom =
      radical (A.map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K))) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_radical hx g
  · intro y hy
    refine ⟨g⁻¹ * y * g, ?_, by simp [mul_assoc]⟩
    have := conj_mem_radical hy g⁻¹
    rwa [inv_inv, ← Submodule.map_comp, ← mulVecLin_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, mulVecLin_one, Submodule.map_id] at this

theorem isRadicalMatrix_flagSpace_iff {d : ℕ} {N : Matrix (Fin 3) (Fin 3) K} :
    IsRadicalMatrix (flagSpace 3 K d) N ↔
      ∀ i j : Fin 3, (d ≤ (i : ℕ) ∨ (j : ℕ) < d) → N i j = 0 := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases hij with hi | hj
    · have := mem_flagSpace.1 (h1 (Pi.single j 1)) i hi
      rwa [mulVec_single_one] at this
    · have hmem : (Pi.single j 1 : Fin 3 → K) ∈ flagSpace 3 K d := by
        rw [mem_flagSpace]
        intro c hc
        have hcj : c ≠ j := fun h => by
          subst h
          omega
        simp [hcj]
      have := congrFun (h2 _ hmem) i
      rwa [mulVec_single_one] at this
  · intro h
    refine ⟨fun v => mem_flagSpace.2 fun c hc => ?_, fun v hv => ?_⟩
    · simp only [mulVec, dotProduct]
      exact Finset.sum_eq_zero fun j _ => by rw [h c j (Or.inl hc), zero_mul]
    · ext i
      simp only [mulVec, dotProduct, Pi.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : (j : ℕ) < d
      · rw [h i j (Or.inr hj), zero_mul]
      · rw [mem_flagSpace.1 hv j (not_lt.1 hj), mul_zero]

@[expose] noncomputable def radicalOneEquiv :
    {N : Matrix (Fin 3) (Fin 3) K // IsRadicalMatrix (flagSpace 3 K 1) N} ≃ K × K where
  toFun N := (N.1 0 1, N.1 0 2)
  invFun x := ⟨!![0, x.1, x.2; 0, 0, 0; 0, 0, 0], isRadicalMatrix_flagSpace_iff.2 fun i j hij => by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢⟩
  left_inv N := by
    have h := isRadicalMatrix_flagSpace_iff.1 N.2
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> exact (h _ _ (by simp)).symm
  right_inv x := by simp

@[expose] noncomputable def radicalTwoEquiv :
    {N : Matrix (Fin 3) (Fin 3) K // IsRadicalMatrix (flagSpace 3 K 2) N} ≃ K × K where
  toFun N := (N.1 0 2, N.1 1 2)
  invFun x := ⟨!![0, 0, x.1; 0, 0, x.2; 0, 0, 0], isRadicalMatrix_flagSpace_iff.2 fun i j hij => by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢⟩
  left_inv N := by
    have h := isRadicalMatrix_flagSpace_iff.1 N.2
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> exact (h _ _ (by simp)).symm
  right_inv x := by simp

section Card

variable [CharP K 2]

theorem card_radical_flagSpace {d : ℕ} (hd : d = 1 ∨ d = 2) :
    Nat.card (radical (flagSpace 3 K d)) = Nat.card K ^ 2 := by
  rw [Nat.card_congr (radicalEquiv _)]
  rcases hd with rfl | rfl
  · rw [Nat.card_congr radicalOneEquiv, Nat.card_prod, pow_two]
  · rw [Nat.card_congr radicalTwoEquiv, Nat.card_prod, pow_two]

theorem card_radical {A : Submodule K (Fin 3 → K)} (hA : finrank K A = 1 ∨ finrank K A = 2) :
    Nat.card (radical A) = Nat.card K ^ 2 := by
  obtain ⟨g, hg⟩ := exists_map_flagSpace_eq A
  rw [← hg, ← map_conj_radical, Subgroup.card_map_of_injective (MulAut.conj g).injective,
    card_radical_flagSpace hA]

end Card

theorem le_of_radical_le [CharP K 2] {A B : Submodule K (Fin 3 → K)} (hA : finrank K A < 3)
    (h : radical A ≤ radical B) : A ≤ B := by
  classical
  have hperp : finrank K (dotOrth A) ≠ 0 := by
    rw [finrank_dotOrth]
    omega
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := dotOrth A)
    (fun h' => hperp (by rw [h', finrank_bot]))
  obtain ⟨j, hj⟩ : ∃ j, f j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hf0 (funext hall)
  intro a ha
  have hN : IsRadicalMatrix A (vecMulVec a f) := by
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [vecMulVec_mulVec, op_smul_eq_smul]
      exact A.smul_mem _ ha
    · rw [vecMulVec_mulVec, op_smul_eq_smul, mem_dotOrth.1 hf v hv, zero_smul]
  obtain ⟨g, hg, hgN⟩ := (exists_mem_radical_iff _).1 ⟨_, hN, rfl⟩
  have hB := (mem_radical.1 (h hg)).1 (Pi.single j 1)
  rw [hgN, add_sub_cancel_left, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_single_one] at hB
  have := B.smul_mem (f j)⁻¹ hB
  rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at this

theorem eq_of_radical_eq [CharP K 2] {A B : Submodule K (Fin 3 → K)} (hA : finrank K A < 3)
    (hB : finrank K B < 3) (h : radical A = radical B) : A = B :=
  le_antisymm (le_of_radical_le hA h.le) (le_of_radical_le hB h.ge)

section Classification

variable [CharP K 2]

theorem unitriangular_sq_apply {u : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K) :
    ((u ^ 2 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 =
      (u : Matrix (Fin 3) (Fin 3) K) 0 1 * (u : Matrix (Fin 3) (Fin 3) K) 1 2 := by
  obtain ⟨hl, hd⟩ := mem_unitriangular.1 hu
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_two, mul_apply, Fin.sum_univ_three]
  rw [hd 0, hd 2, one_mul, mul_one]
  linear_combination (u : Matrix (Fin 3) (Fin 3) K) 0 2 * (CharTwo.two_eq_zero : (2 : K) = 0)

omit [CharP K 2] in
theorem unitriangular_mul_apply_zero_one {u v : SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) (hv : v ∈ unitriangular 3 K) :
    ((u * v : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 =
      (u : Matrix (Fin 3) (Fin 3) K) 0 1 + (v : Matrix (Fin 3) (Fin 3) K) 0 1 := by
  obtain ⟨hul, hud⟩ := mem_unitriangular.1 hu
  obtain ⟨hvl, hvd⟩ := mem_unitriangular.1 hv
  rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_three, hud 0, hvd 1,
    hvl 2 1 (by decide)]
  ring

omit [CharP K 2] in
theorem unitriangular_mul_apply_one_two {u v : SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) (hv : v ∈ unitriangular 3 K) :
    ((u * v : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 =
      (u : Matrix (Fin 3) (Fin 3) K) 1 2 + (v : Matrix (Fin 3) (Fin 3) K) 1 2 := by
  obtain ⟨hul, hud⟩ := mem_unitriangular.1 hu
  obtain ⟨hvl, hvd⟩ := mem_unitriangular.1 hv
  rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_three, hul 1 0 (by decide), hud 1,
    hvd 2]
  ring

omit [CharP K 2] in
theorem mem_radical_two_of_unitriangular {u : SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) (h01 : (u : Matrix (Fin 3) (Fin 3) K) 0 1 = 0) :
    u ∈ radical (flagSpace 3 K 2) := by
  obtain ⟨hl, hd⟩ := mem_unitriangular.1 hu
  rw [mem_radical, isRadicalMatrix_flagSpace_iff]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
    first
    | exact sub_eq_zero.2 (hd _)
    | exact hd _
    | exact hl _ _ (by decide)
    | exact h01

omit [CharP K 2] in
theorem mem_radical_one_of_unitriangular {u : SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) (h12 : (u : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) :
    u ∈ radical (flagSpace 3 K 1) := by
  obtain ⟨hl, hd⟩ := mem_unitriangular.1 hu
  rw [mem_radical, isRadicalMatrix_flagSpace_iff]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
    first
    | exact sub_eq_zero.2 (hd _)
    | exact hd _
    | exact hl _ _ (by decide)
    | exact h12

theorem le_radical_of_le_unitriangular {E : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hEU : E ≤ unitriangular 3 K) (hsq : ∀ x ∈ E, x ^ 2 = 1) :
    E ≤ radical (flagSpace 3 K 1) ∨ E ≤ radical (flagSpace 3 K 2) := by
  have hac : ∀ x ∈ E, (x : Matrix (Fin 3) (Fin 3) K) 0 1 * (x : Matrix (Fin 3) (Fin 3) K) 1 2 =
      0 := by
    intro x hx
    rw [← unitriangular_sq_apply (hEU hx), hsq x hx]
    simp
  by_cases h : ∀ x ∈ E, (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0
  · exact Or.inl fun x hx => mem_radical_one_of_unitriangular (hEU hx) (h x hx)
  · right
    push Not at h
    obtain ⟨y, hy, hy12⟩ := h
    intro x hx
    refine mem_radical_two_of_unitriangular (hEU hx) ?_
    by_contra hx01
    have hx12 : (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 :=
      (mul_eq_zero.1 (hac x hx)).resolve_left hx01
    have hy01 : (y : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 :=
      (mul_eq_zero.1 (hac y hy)).resolve_right hy12
    have hxy := hac (x * y) (E.mul_mem hx hy)
    rw [unitriangular_mul_apply_zero_one (hEU hx) (hEU hy),
      unitriangular_mul_apply_one_two (hEU hx) (hEU hy), hx12, hy01, add_zero, zero_add] at hxy
    exact (mul_ne_zero hx01 hy12) hxy

theorem exists_eq_radical [Finite K] {E : Subgroup (SpecialLinearGroup (Fin 3) K)}
    [hE : IsElementaryAbelian 2 E] (hcard : Nat.card E = Nat.card K ^ 2) :
    ∃ A : Submodule K (Fin 3 → K), (finrank K A = 1 ∨ finrank K A = 2) ∧ E = radical A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 E := IsElementaryAbelian.isPGroup 2 E
  obtain ⟨T, hT⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  obtain ⟨S, hES⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) K) S T
  set E' := E.map (MulAut.conj g).toMonoidHom with hE'
  have hE'U : E' ≤ unitriangular 3 K := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hT, ← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hES hx)
  have hsq : ∀ x ∈ E', x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) x hx, map_one]
  have hcard' : Nat.card E' = Nat.card K ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  obtain ⟨d, hd, hEd⟩ : ∃ d, (d = 1 ∨ d = 2) ∧ E' = radical (flagSpace 3 K d) := by
    rcases le_radical_of_le_unitriangular hE'U hsq with h | h
    · exact ⟨1, Or.inl rfl, Subgroup.eq_of_le_of_card_ge h
        (by rw [card_radical_flagSpace (Or.inl rfl), hcard'])⟩
    · exact ⟨2, Or.inr rfl, Subgroup.eq_of_le_of_card_ge h
        (by rw [card_radical_flagSpace (Or.inr rfl), hcard'])⟩
  refine ⟨(flagSpace 3 K d).map (mulVecLin ((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K)), ?_, ?_⟩
  · have hinj : Function.Injective (mulVecLin ((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) := by
      have hgg : (g : Matrix (Fin 3) (Fin 3) K) *
          ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one]
      intro v w hvw
      have := congrArg (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) hvw
      simp only [mulVecLin_apply, mulVec_mulVec, hgg, one_mulVec] at this
      exact this
    rw [← (Submodule.equivMapOfInjective _ hinj _).finrank_eq,
      finrank_flagSpace (by omega)]
    exact hd
  · rw [← map_conj_radical, ← hEd, hE', Subgroup.map_map]
    conv_lhs => rw [← Subgroup.map_id E]
    congr 1
    ext x
    simp [mul_assoc]

end Classification

end CFSG.LocalAnalysis.SteinbergCD

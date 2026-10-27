module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.L1232

open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {F : Type} [Field F]

@[expose] def uniM (a b c : F) : Matrix (Fin 3) (Fin 3) F := !![1, a, b; 0, 1, c; 0, 0, 1]

theorem det_uniM (a b c : F) : (uniM a b c).det = 1 := by
  simp [uniM, Matrix.det_fin_three]

theorem uniM_mul (a b c a' b' c' : F) :
    uniM a b c * uniM a' b' c' = uniM (a + a') (b + a * c' + b') (c + c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniM, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uniM_zero : uniM (0 : F) 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniM]

@[expose] def uniGL (a b c : F) : GL (Fin 3) F :=
  ⟨uniM a b c, uniM (-a) (a * c - b) (-c),
    by rw [uniM_mul, ← uniM_zero]; congr 1 <;> ring,
    by rw [uniM_mul, ← uniM_zero]; congr 1 <;> ring⟩

@[expose] def uniSL (a b c : F) : ↥(StatedSL 3 F) :=
  ⟨uniGL a b c, Subgroup.subset_closure (det_uniM a b c)⟩

theorem uniSL_coe (a b c : F) :
    (((uniSL a b c : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = uniM a b c :=
  rfl

theorem uniSL_injective {a b c a' b' c' : F} (h : uniSL a b c = uniSL a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h' := congrArg (fun g : ↥(StatedSL 3 F) => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
  simp only [uniSL_coe] at h'
  have e1 := congrFun (congrFun h' 0) 1
  have e2 := congrFun (congrFun h' 0) 2
  have e3 := congrFun (congrFun h' 1) 2
  simp [uniM] at e1 e2 e3
  exact ⟨e1, e2, e3⟩

@[expose] def Uni (F : Type) [Field F] : Subgroup ↥(StatedSL 3 F) where
  carrier := {g | ∃ a b c : F, g = uniSL a b c}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨a + a', b + a * c' + b', c + c', Subtype.ext (Units.ext (uniM_mul a b c a' b' c'))⟩
  one_mem' := ⟨0, 0, 0, Subtype.ext (Units.ext uniM_zero.symm)⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    exact ⟨-a, a * c - b, -c, Subtype.ext (Units.ext rfl)⟩

theorem uniSL_mem (a b c : F) : uniSL a b c ∈ Uni F := ⟨a, b, c, rfl⟩

theorem card_Uni [Finite F] : Nat.card (Uni F) = Nat.card F ^ 3 := by
  have hb : Function.Bijective fun p : F × F × F => (⟨uniSL p.1 p.2.1 p.2.2,
      uniSL_mem _ _ _⟩ : ↥(Uni F)) := by
    refine ⟨fun p q h => ?_, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := uniSL_injective (congrArg Subtype.val h)
      exact Prod.ext h1 (Prod.ext h2 h3)
    · rintro ⟨_, a, b, c, rfl⟩
      exact ⟨(a, b, c), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hb), Nat.card_prod, Nat.card_prod]
  ring

theorem eq_of_fix_Uni {v : Fin 3 → F}
    (hv : ∀ g ∈ Uni F, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) :
    v 1 = 0 ∧ v 2 = 0 := by
  have h1 := congrFun (hv _ (uniSL_mem 1 0 0)) 0
  have h2 := congrFun (hv _ (uniSL_mem 0 0 1)) 1
  simp [uniSL_coe, uniM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
  exact ⟨h1, h2⟩

theorem fix_e0 (g : ↥(StatedSL 3 F)) (hg : g ∈ Uni F) (x : F) :
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![x, 0, 0] = ![x, 0, 0] := by
  obtain ⟨a, b, c, rfl⟩ := hg
  ext i
  fin_cases i <;> simp [uniSL_coe, uniM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem det_eq_one (g : ↥(StatedSL 3 F)) :
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  have hle : StatedSL 3 F ≤ (Matrix.GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).ker := by
    refine (Subgroup.closure_le _).2 fun A hA => ?_
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hA)
  have h := hle g.2
  rw [MonoidHom.mem_ker] at h
  have := congrArg Units.val h
  rwa [Matrix.GeneralLinearGroup.val_det_apply] at this

section Four

variable [Fintype F]

theorem two_eq_zero (hF : Fintype.card F = 4) : (2 : F) = 0 := by
  have h := FiniteField.cast_card_eq_zero F
  rw [hF] at h
  have h4 : (2 : F) * 2 = 0 := by norm_num at h ⊢; exact h
  exact mul_self_eq_zero.1 h4

theorem pow_four_eq (hF : Fintype.card F = 4) (x : F) : x ^ 4 = x := by
  have := FiniteField.pow_card x
  rwa [hF] at this

theorem eq_one_of_pow_five (hF : Fintype.card F = 4) {x : F} (h : x ^ 5 = 1) : x = 1 := by
  have h4 := pow_four_eq hF x
  have h52 : x ^ 5 = x ^ 2 := by
    rw [show x ^ 5 = x ^ 4 * x by ring, h4]
    ring
  have h2 : x ^ 2 = 1 := by rw [← h52]; exact h
  calc x = x ^ 4 := h4.symm
    _ = (x ^ 2) ^ 2 := by ring
    _ = 1 := by rw [h2, one_pow]

theorem card_SL3 (hF : Fintype.card F = 4) : Nat.card ↥(StatedSL 3 F) = 60480 := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv, Matrix.card_SL_field 3, hF,
    Fin.prod_univ_three]
  norm_num

theorem exists_omega (hF : Fintype.card F = 4) : ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  classical
  obtain ⟨ω, hω⟩ : ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hall x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hF] at this
    have h2 := Finset.card_le_two (a := (0 : F)) (b := 1)
    omega
  refine ⟨ω, ?_⟩
  have h4 := pow_four_eq hF ω
  have h3 : ω ^ 3 = 1 := by
    have : ω * (ω ^ 3 - 1) = 0 := by rw [mul_sub, ← pow_succ', h4]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hω.1
    · exact sub_eq_zero.1 h
  have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by rw [← sub_eq_zero.2 h3]; ring
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hω.2
  · exact h

end Four

section Five

variable {ω : F}

@[expose] def dM (ω : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 0, 1; 0, 1, ω]

@[expose] def d2M (ω : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 1, ω; 0, ω, ω]

@[expose] def d4M (ω : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, ω, 1; 0, 1, 0]

theorem dM_mul_dM (h2 : (2 : F) = 0) (hω : ω ^ 2 + ω + 1 = 0) : dM ω * dM ω = d2M ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM, d2M, Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination hω - ω * h2

theorem d2M_mul_d2M (h2 : (2 : F) = 0) (hω : ω ^ 2 + ω + 1 = 0) : d2M ω * d2M ω = d4M ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d2M, d4M, Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination hω - ω * h2
  · linear_combination hω - h2
  · linear_combination hω - h2
  · linear_combination h2 * ω ^ 2

theorem d4M_mul_dM (h2 : (2 : F) = 0) : d4M ω * dM ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d4M, dM, Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination h2 * ω

theorem dM_mul_d4M (h2 : (2 : F) = 0) : dM ω * d4M ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d4M, dM, Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination h2 * ω

theorem det_dM (h2 : (2 : F) = 0) : (dM ω).det = 1 := by
  simp [dM, Matrix.det_fin_three]
  linear_combination -h2

@[expose] def dGL (h2 : (2 : F) = 0) (ω : F) : GL (Fin 3) F :=
  ⟨dM ω, d4M ω, dM_mul_d4M h2, d4M_mul_dM h2⟩

@[expose] def dSL (h2 : (2 : F) = 0) (ω : F) : ↥(StatedSL 3 F) :=
  ⟨dGL h2 ω, Subgroup.subset_closure (det_dM h2)⟩

theorem dSL_coe (h2 : (2 : F) = 0) :
    (((dSL h2 ω : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dM ω :=
  rfl

theorem dM_pow_five (h2 : (2 : F) = 0) (hω : ω ^ 2 + ω + 1 = 0) : dM ω ^ 5 = 1 := by
  have e : dM ω ^ 5 = (dM ω * dM ω) * (dM ω * dM ω) * dM ω := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e, dM_mul_dM h2 hω, d2M_mul_d2M h2 hω, d4M_mul_dM h2]

theorem dSL_pow_five (h2 : (2 : F) = 0) (hω : ω ^ 2 + ω + 1 = 0) : dSL h2 ω ^ 5 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, dSL_coe, dM_pow_five h2 hω]
  rfl

theorem dSL_ne_one (h2 : (2 : F) = 0) : dSL h2 ω ≠ 1 := by
  intro h
  have := congrArg (fun g : ↥(StatedSL 3 F) =>
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1) h
  simp [dSL_coe, dM] at this

theorem dSL_fix (h2 : (2 : F) = 0) (x : F) :
    (((dSL h2 ω : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![x, 0, 0] =
      ![x, 0, 0] := by
  ext i
  fin_cases i <;> simp [dSL_coe, dM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end Five

section Norm

theorem mulVec_e0_of_lower {M : Matrix (Fin 3) (Fin 3) F} (h10 : M 1 0 = 0) (h20 : M 2 0 = 0)
    (x : F) : M *ᵥ ![x, 0, 0] = ![M 0 0 * x, 0, 0] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h20, mul_comm]

theorem mulVec_two_of_lower {M : Matrix (Fin 3) (Fin 3) F} (h20 : M 2 0 = 0) (h21 : M 2 1 = 0)
    (w : Fin 3 → F) : (M *ᵥ w) 2 = M 2 2 * w 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h20, h21]

theorem pow_mulVec_e0 {M : Matrix (Fin 3) (Fin 3) F} (h10 : M 1 0 = 0) (h20 : M 2 0 = 0)
    (n : ℕ) : (M ^ n) *ᵥ ![1, 0, 0] = ![M 0 0 ^ n, 0, 0] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, mulVec_e0_of_lower h10 h20, mul_one]
    have e : ![M 0 0, (0 : F), 0] = M 0 0 • ![(1 : F), 0, 0] := by
      ext i; fin_cases i <;> simp
    rw [e, Matrix.mulVec_smul, ih]
    ext i; fin_cases i <;> simp [pow_succ, mul_comm]

theorem pow_mulVec_two {M : Matrix (Fin 3) (Fin 3) F} (h20 : M 2 0 = 0) (h21 : M 2 1 = 0)
    (n : ℕ) (w : Fin 3 → F) : ((M ^ n) *ᵥ w) 2 = M 2 2 ^ n * w 2 := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, ih, mulVec_two_of_lower h20 h21, pow_succ]
    ring

abbrev mat (g : ↥(StatedSL 3 F)) : Matrix (Fin 3) (Fin 3) F := ((g : GL (Fin 3) F) : Matrix _ _ F)

theorem mat_mul (g h : ↥(StatedSL 3 F)) : mat (g * h) = mat g * mat h := rfl

theorem mat_pow (g : ↥(StatedSL 3 F)) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  simp [mat, Units.val_pow_eq_pow_val]

theorem mat_conj (m g : ↥(StatedSL 3 F)) : mat g * mat m = mat m * mat (m⁻¹ * g * m) := by
  rw [← mat_mul, ← mat_mul]
  congr 1
  group

variable [Fintype F]

theorem eq_one_of_normalizes (hF : Fintype.card F = 4) {m : ↥(StatedSL 3 F)}
    (hm : ∀ u ∈ Uni F, m * u * m⁻¹ ∈ Uni F) (hm5 : m ^ 5 = 1) : m = 1 := by
  have hinv : ∀ u ∈ Uni F, m⁻¹ * u * m ∈ Uni F := by
    intro u hu
    have e : m⁻¹ = m ^ 4 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', hm5]
    have h4 : ∀ k : ℕ, m ^ k * u * (m ^ k)⁻¹ ∈ Uni F := by
      intro k
      induction k with
      | zero => simpa using hu
      | succ k ih =>
        have := hm _ ih
        simpa [pow_succ', mul_assoc] using this
    have := h4 4
    rwa [← e, inv_inv] at this
  have h0 : mat m 1 0 = 0 ∧ mat m 2 0 = 0 := by
    have hfix : ∀ g ∈ Uni F, mat g *ᵥ (mat m *ᵥ ![1, 0, 0]) = mat m *ᵥ ![1, 0, 0] := by
      intro g hg
      rw [Matrix.mulVec_mulVec, mat_conj m g, ← Matrix.mulVec_mulVec, fix_e0 _ (hinv g hg)]
    have := eq_of_fix_Uni hfix
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h21 : mat m 2 1 = 0 := by
    obtain ⟨a, b, c, hg'⟩ := hinv _ (uniSL_mem 0 0 1)
    have e1 := mat_conj m (uniSL 0 0 1)
    rw [hg'] at e1
    have e2 := congrFun (congrFun e1 1) 1
    simp only [mat, uniSL_coe] at e2
    simp [uniM, Matrix.mul_apply, Fin.sum_univ_three] at e2
    have e3 : mat m 2 1 = mat m 1 0 * a := by linear_combination e2
    rw [e3, h0.1, zero_mul]
  have hM5 : mat m ^ 5 = 1 := by
    rw [← mat_pow, hm5]
    rfl
  have h00 : mat m 0 0 = 1 := by
    have := pow_mulVec_e0 h0.1 h0.2 5
    rw [hM5, Matrix.one_mulVec] at this
    have h := congrFun this 0
    simp at h
    exact eq_one_of_pow_five hF h.symm
  have h22 : mat m 2 2 = 1 := by
    have := pow_mulVec_two h0.2 h21 5 ![0, 0, 1]
    rw [hM5, Matrix.one_mulVec] at this
    simp at this
    exact eq_one_of_pow_five hF this.symm
  have h11 : mat m 1 1 = 1 := by
    have hd := det_eq_one m
    rw [Matrix.det_fin_three] at hd
    simp only [mat] at h0 h21 h00 h22
    rw [h0.1, h0.2, h21, h00, h22] at hd
    simpa using hd
  have hmU : m ∈ Uni F := by
    refine ⟨mat m 0 1, mat m 0 2, mat m 1 2, Subtype.ext (Units.ext ?_)⟩
    show mat m = uniM (mat m 0 1) (mat m 0 2) (mat m 1 2)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uniM, h0.1, h0.2, h21, h00, h11, h22]
  have hcard : Nat.card (Uni F) = 64 := by
    rw [card_Uni, Nat.card_eq_fintype_card, hF]
    norm_num
  have h64 : (⟨m, hmU⟩ : ↥(Uni F)) ^ 64 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have h1 : (⟨m, hmU⟩ : ↥(Uni F)) ^ 5 = 1 := Subtype.ext (by simpa using hm5)
  have hord := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h64) (orderOf_dvd_of_pow_eq_one h1)
  have hone : (⟨m, hmU⟩ : ↥(Uni F)) = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.dvd_one.1 (by simpa using hord)
  exact congrArg Subtype.val hone

end Norm

end CFSG.Quasithin.H13.L1232

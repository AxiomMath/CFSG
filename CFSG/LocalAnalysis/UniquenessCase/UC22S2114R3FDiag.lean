module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def uc22s2114r3f_diagUnits {n : ℕ} (a b : Kˣ) (i : Fin n) : Kˣ :=
  if (i : ℕ) = 0 then a else if (i : ℕ) = 1 then b else if (i : ℕ) = 2 then (a * b)⁻¹ else 1

@[expose] def uc22s2114r3f_diagGL {n : ℕ} (a b : Kˣ) : GL (Fin n) K :=
  ⟨diagonal fun i => (uc22s2114r3f_diagUnits a b i : K),
    diagonal fun i => ((uc22s2114r3f_diagUnits a b i)⁻¹ : Kˣ),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact Units.mul_inv _,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact Units.inv_mul _⟩

theorem uc22s2114r3f_coe_diagGL {n : ℕ} (a b : Kˣ) :
    ((uc22s2114r3f_diagGL a b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => (uc22s2114r3f_diagUnits a b i : K) :=
  rfl

theorem uc22s2114r3f_diagGL_one {n : ℕ} : (uc22s2114r3f_diagGL (1 : Kˣ) 1 : GL (Fin n) K) = 1 := by
  refine Units.ext ?_
  rw [uc22s2114r3f_coe_diagGL, Units.val_one, ← diagonal_one]
  congr 1
  funext i
  simp [uc22s2114r3f_diagUnits]

theorem uc22s2114r3f_diagGL_mul {n : ℕ} (a a' b b' : Kˣ) :
    (uc22s2114r3f_diagGL (a * a') (b * b') : GL (Fin n) K) =
      uc22s2114r3f_diagGL a b * uc22s2114r3f_diagGL a' b' := by
  refine Units.ext ?_
  rw [Units.val_mul, uc22s2114r3f_coe_diagGL, uc22s2114r3f_coe_diagGL, uc22s2114r3f_coe_diagGL,
    diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Units.val_mul]
  congr 1
  unfold uc22s2114r3f_diagUnits
  split_ifs
  · rfl
  · rfl
  · rw [mul_mul_mul_comm, mul_inv]
  · rw [mul_one]

theorem uc22s2114r3f_norm_diagUnits (h : UnitaryFieldData p f K) {n : ℕ} {a b : Kˣ}
    (ha : h.norm (a : K) = 1) (hb : h.norm (b : K) = 1) (i : Fin n) :
    h.norm (uc22s2114r3f_diagUnits a b i : K) = 1 := by
  unfold uc22s2114r3f_diagUnits
  split_ifs
  · exact ha
  · exact hb
  · rw [Units.val_inv_eq_inv_val, Units.val_mul, norm_inv_eq h, norm_mul_eq h, ha, hb, mul_one,
      inv_one]
  · rw [Units.val_one, UnitaryFieldData.norm, map_one, mul_one]

theorem uc22s2114r3f_prod_diagUnits {n : ℕ} (hn : 3 ≤ n) (a b : Kˣ) :
    ∏ i : Fin n, uc22s2114r3f_diagUnits a b i = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [uc22s2114r3f_diagUnits, Fin.val_succ, Fin.val_zero]
  simp

theorem uc22s2114r3f_diagGL_mem (h : UnitaryFieldData p f K) {n : ℕ} (hn : 3 ≤ n) {a b : Kˣ}
    (ha : h.norm (a : K) = 1) (hb : h.norm (b : K) = 1) :
    uc22s2114r3f_diagGL a b ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · rw [Units.val_one, Matrix.mul_one, uc22s2114r3f_coe_diagGL, diagonal_map (map_zero _),
      diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact uc22s2114r3f_norm_diagUnits h ha hb i
  · rw [uc22s2114r3f_coe_diagGL, det_diagonal, ← Units.coe_prod,
      uc22s2114r3f_prod_diagUnits hn, Units.val_one]

@[expose] noncomputable def uc22s2114r3f_diagSU (h : UnitaryFieldData p f K) {n : ℕ} (hn : 3 ≤ n)
    (μ : Subgroup Kˣ) (hμ : ∀ s ∈ μ, h.norm (s : K) = 1) :
    (Fin 2 → μ) →* gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) where
  toFun s := ⟨uc22s2114r3f_diagGL (s 0 : Kˣ) (s 1 : Kˣ),
    uc22s2114r3f_diagGL_mem h hn (hμ _ (s 0).2) (hμ _ (s 1).2)⟩
  map_one' := Subtype.ext uc22s2114r3f_diagGL_one
  map_mul' _ _ := Subtype.ext (uc22s2114r3f_diagGL_mul _ _ _ _)

theorem uc22s2114r3f_coe_diagSU (h : UnitaryFieldData p f K) {n : ℕ} (hn : 3 ≤ n)
    (μ : Subgroup Kˣ) (hμ : ∀ s ∈ μ, h.norm (s : K) = 1) (s : Fin 2 → μ) :
    (((uc22s2114r3f_diagSU h hn μ hμ s :
        gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal fun i : Fin n => if (i : ℕ) = 0 then ((s 0 : Kˣ) : K) else
        if (i : ℕ) = 1 then ((s 1 : Kˣ) : K) else
          if (i : ℕ) = 2 then (((s 0 : Kˣ) : K) * ((s 1 : Kˣ) : K))⁻¹ else 1 := by
  change diagonal (fun i => (uc22s2114r3f_diagUnits (s 0 : Kˣ) (s 1 : Kˣ) i : K)) = _
  congr 1
  funext i
  unfold uc22s2114r3f_diagUnits
  split_ifs <;> simp

theorem uc22s2114r3f_diagSU_injective (h : UnitaryFieldData p f K) {n : ℕ} (hn : 4 ≤ n)
    (μ : Subgroup Kˣ) (hμ : ∀ s ∈ μ, h.norm (s : K) = 1) :
    Function.Injective ((QuotientGroup.mk' (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n)).comp
        (uc22s2114r3f_diagSU h (by omega) μ hμ)) := by
  refine (injective_iff_map_eq_one _).2 fun s hs => ?_
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hs
  obtain ⟨c, -, -, hc⟩ := hs
  have hM := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
  simp only [uc22s2114r3f_coe_diagSU, GeneralLinearGroup.coe_scalar, scalar_apply] at hM
  have hd := diagonal_injective hM
  have h3 : (1 : K) = c := by simpa using congrFun hd ⟨3, by omega⟩
  have h0 : ((s 0 : Kˣ) : K) = c := by simpa using congrFun hd ⟨0, by omega⟩
  have h1 : ((s 1 : Kˣ) : K) = c := by simpa using congrFun hd ⟨1, by omega⟩
  have hs0 : s 0 = 1 := Subtype.ext (Units.ext (h0.trans h3.symm))
  have hs1 : s 1 = 1 := Subtype.ext (Units.ext (h1.trans h3.symm))
  funext i
  fin_cases i
  · exact hs0
  · exact hs1

theorem uc22s2114r3f_primeFormFieldHom_diagSU (h : UnitaryFieldData p f K) {n : ℕ} (hn : 3 ≤ n)
    (μ : Subgroup Kˣ) (hμ : ∀ s ∈ μ, h.norm (s : K) = 1)
    (hC : IsPrimeFormGram (1 : GL (Fin n) K)) (σ : K ≃+* K) (κ : μ →* μ)
    (hκ : ∀ s : μ, ((κ s : Kˣ) : K) = σ ((s : Kˣ) : K)) (s : Fin 2 → μ) :
    primeFormFieldHom h hC σ ((uc22s2114r3f_diagSU h hn μ hμ s :
        gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
        primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      ((uc22s2114r3f_diagSU h hn μ hμ (fun i => κ (s i)) :
        gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
        primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  change primeFormFieldAut h hC σ _ = _
  rw [primeFormFieldAut_mk]
  congr 1
  refine Subtype.ext ?_
  change glAut σ ((uc22s2114r3f_diagSU h hn μ hμ s :
    gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) = _
  refine Units.ext ?_
  rw [coe_glAut, uc22s2114r3f_coe_diagSU, uc22s2114r3f_coe_diagSU, diagonal_map (map_zero σ)]
  congr 1
  funext i
  simp only [hκ]
  split_ifs <;> simp

end CFSG.LocalAnalysis.UniquenessCase.UC22

module

public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.Item47WitnessG2

public section

namespace CFSG.RankThree.PartTwo.Sec4.WitnessU4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open Matrix

variable {p f : ℕ} {K : Type} [Field K]

section Transfer

variable {h : UnitaryFieldData p f K} {m : ℕ} {C : GL (Fin m) K}

theorem hasLocalWitness_primeFormFieldHom_of (hC : IsPrimeFormGram C) (φ : K ≃+* K)
    {s₁ s₂ t : gramSU h (C : Matrix (Fin m) (Fin m) K)}
    (hs₁ : primeFormFieldSU h hC φ s₁ = s₁) (hs₂ : primeFormFieldSU h hC φ s₂ = s₂)
    (h₁3 : s₁ ^ 3 = 1) (h₂3 : s₂ ^ 3 = 1) (hcomm : s₁ * s₂ = s₂ * s₁)
    (hs₁Z : s₁ ∉ normOneScalars h (gramSU h (C : Matrix (Fin m) (Fin m) K)) m)
    (ht₁ : t * s₁ = s₁ * t) (ht₂ : t * s₂ ≠ s₂ * t)
    {U₀ : Subgroup (gramSU h (C : Matrix (Fin m) (Fin m) K))} (hU2 : IsPGroup 2 U₀)
    (hU1 : ∃ u ∈ U₀, u ∉ normOneScalars h (gramSU h (C : Matrix (Fin m) (Fin m) K)) m)
    (hUs₁ : ∀ u ∈ U₀, s₁ * u * s₁⁻¹ ∈ U₀) (hUs₂ : ∀ u ∈ U₀, s₂ * u * s₂⁻¹ ∈ U₀)
    (hUφ : ∀ u ∈ U₀, primeFormFieldSU h hC φ u ∈ U₀) :
    HasLocalWitness (primeFormFieldHom h hC φ) := by
  set Z := normOneScalars h (gramSU h (C : Matrix (Fin m) (Fin m) K)) m
  have hfix : ∀ s, primeFormFieldSU h hC φ s = s →
      primeFormFieldHom h hC φ (s : primeFormP h (C : Matrix (Fin m) (Fin m) K)) = s := by
    intro s hs
    change primeFormFieldAut h hC φ (s : primeFormP h (C : Matrix (Fin m) (Fin m) K)) = s
    rw [primeFormFieldAut_mk, hs]
  refine ⟨(s₁ : primeFormP h (C : Matrix (Fin m) (Fin m) K)),
    (s₂ : primeFormP h (C : Matrix (Fin m) (Fin m) K)), U₀.map (QuotientGroup.mk' Z),
    hfix s₁ hs₁, hfix s₂ hs₂, ?_, ?_, ?_, ?_, ?_, hU2.map _, ?_, ?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_pow, h₁3, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_pow, h₂3, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_mul, hcomm, QuotientGroup.mk_mul]
  · intro h1
    exact hs₁Z ((QuotientGroup.eq_one_iff s₁).mp h1)
  · rintro ⟨j, hj⟩
    simp only at hj
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hj
    have hz := Subgroup.mem_center_iff.mp (normOneScalars_le_center h _ m hj) t
    apply ht₂
    have hc1 : Commute t (s₁ ^ j) := Commute.zpow_right ht₁ j
    have hc2 : Commute t ((s₁ ^ j)⁻¹ * s₂) := hz
    have hs₂eq : s₂ = s₁ ^ j * ((s₁ ^ j)⁻¹ * s₂) := by group
    rw [hs₂eq]
    exact (hc1.mul_right hc2).eq
  · intro h1
    obtain ⟨u, hu, huZ⟩ := hU1
    have hmem : QuotientGroup.mk' Z u ∈ U₀.map (QuotientGroup.mk' Z) := ⟨u, hu, rfl⟩
    rw [h1, Subgroup.mem_bot] at hmem
    exact huZ ((QuotientGroup.eq_one_iff u).mp hmem)
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨s₁ * u * s₁⁻¹, hUs₁ u hu, by simp only [map_mul, map_inv]; rfl⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨s₂ * u * s₂⁻¹, hUs₂ u hu, by simp only [map_mul, map_inv]; rfl⟩
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨primeFormFieldSU h hC φ u, hUφ u hu, ?_⟩
    change ((primeFormFieldSU h hC φ u : gramSU h _) : primeFormP h _) =
      primeFormFieldAut h hC φ (u : primeFormP h (C : Matrix (Fin m) (Fin m) K))
    rw [primeFormFieldAut_mk]

end Transfer

section Four

variable (h : UnitaryFieldData p f K)

theorem mem_gramSU_one {g : GL (Fin 4) K} :
    g ∈ gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ↔
      ((g : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * g = 1 ∧
        (g : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [mem_gramSU, Units.val_one, Matrix.mul_one]

@[expose] noncomputable def suMk (M : Matrix (Fin 4) (Fin 4) K) (hM : (M.map h.bar)ᵀ * M = 1)
    (hdet : M.det = 1) : gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
  ⟨⟨M, (M.map h.bar)ᵀ, mul_eq_one_comm.mp hM, hM⟩, (mem_gramSU_one h).mpr ⟨hM, hdet⟩⟩

theorem coe_suMk (M : Matrix (Fin 4) (Fin 4) K) (hM : (M.map h.bar)ᵀ * M = 1)
    (hdet : M.det = 1) :
    (((suMk h M hM hdet : gramSU h _) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = M :=
  rfl

variable {h}

theorem gramSU_ext {s s' : gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)}
    (hss' : ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((s' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    s = s' :=
  Subtype.ext (Units.ext hss')

theorem not_mem_normOneScalars_of_ne_zero
    {s : gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)} {i j : Fin 4} (hij : i ≠ j)
    (hs : ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j ≠ 0) :
    s ∉ normOneScalars h (gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) 4 := by
  rintro ⟨c, -, -, hc⟩
  apply hs
  rw [hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

theorem not_mem_normOneScalars_of_ne
    {s : gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)} {i j : Fin 4}
    (hs : ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i ≠
      ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) j j) :
    s ∉ normOneScalars h (gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) 4 := by
  rintro ⟨c, -, -, hc⟩
  apply hs
  rw [hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Matrix.diagonal_apply_eq]

theorem coe_primeFormFieldSU (hC : IsPrimeFormGram (1 : GL (Fin 4) K)) (φ : K ≃+* K)
    (s : gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    (((primeFormFieldSU h hC φ s : gramSU h _) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ :=
  rfl

end Four

section Transvection

@[expose] def transvMat (a : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1 + a, a, 0, 0; a, 1 + a, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem transvMat_mul [CharP K 2] (a b : K) : transvMat a * transvMat b = transvMat (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvMat, Matrix.mul_apply, Fin.sum_univ_four] <;> grind

theorem transvMat_zero : transvMat (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvMat]

theorem transvMat_map (φ : K →+* K) (a : K) : (transvMat a).map φ = transvMat (φ a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvMat]

variable {h : UnitaryFieldData p f K}

theorem transvMat_unitary [CharP K 2] {a : K} (ha : h.bar a = a) :
    ((transvMat a).map h.bar)ᵀ * transvMat a = 1 := by
  rw [transvMat_map, ha]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvMat, Matrix.mul_apply, Fin.sum_univ_four] <;> grind

theorem det_transvMat [CharP K 2] (a : K) : (transvMat a).det = 1 := by
  simp [transvMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  grind

variable (h) in
@[expose] def transvGroup [CharP K 2] :
    Subgroup (gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) where
  carrier := {u | ∃ a, h.bar a = a ∧
    ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = transvMat a}
  mul_mem' := by
    rintro u v ⟨a, ha, hu⟩ ⟨b, hb, hv⟩
    refine ⟨a + b, by rw [map_add, ha, hb], ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, hu, hv, transvMat_mul]
  one_mem' := ⟨0, map_zero _, by rw [transvMat_zero]; rfl⟩
  inv_mem' := by
    rintro u ⟨a, ha, hu⟩
    have huu : u * u = 1 := gramSU_ext (by
      rw [Subgroup.coe_mul, Units.val_mul, hu, transvMat_mul, CharTwo.add_self_eq_zero,
        transvMat_zero]
      rfl)
    refine ⟨a, ha, ?_⟩
    rw [inv_eq_of_mul_eq_one_right huu, hu]

theorem isPGroup_transvGroup [CharP K 2] : IsPGroup 2 (transvGroup h) := by
  rintro ⟨u, a, -, hu⟩
  refine ⟨1, ?_⟩
  rw [pow_one, pow_two]
  refine Subtype.ext (gramSU_ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, hu, transvMat_mul,
    CharTwo.add_self_eq_zero, transvMat_zero]
  rfl

theorem exists_mem_transvGroup_not_mem [CharP K 2] :
    ∃ u ∈ transvGroup h,
      u ∉ normOneScalars h (gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) 4 := by
  refine ⟨suMk h (transvMat 1) (transvMat_unitary (map_one h.bar)) (det_transvMat 1),
    ⟨1, map_one h.bar, rfl⟩, not_mem_normOneScalars_of_ne_zero (i := 0) (j := 1) (by decide) ?_⟩
  rw [coe_suMk]
  simp [transvMat]

theorem primeFormFieldSU_mem_transvGroup [CharP K 2] (hC : IsPrimeFormGram (1 : GL (Fin 4) K))
    (φ : K ≃+* K) {u : gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)}
    (hu : u ∈ transvGroup h) : primeFormFieldSU h hC φ u ∈ transvGroup h := by
  obtain ⟨a, ha, hua⟩ := hu
  refine ⟨φ a, by rw [← map_bar_comm h φ, ha], ?_⟩
  rw [coe_primeFormFieldSU, hua]
  exact transvMat_map (φ : K →+* K) a

theorem conj_mem_transvGroup [CharP K 2]
    {s : gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)}
    (hs : ∀ a, h.bar a = a → ∃ b, h.bar b = b ∧
      ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * transvMat a =
        transvMat b * ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    {u : gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)} (hu : u ∈ transvGroup h) :
    s * u * s⁻¹ ∈ transvGroup h := by
  obtain ⟨a, ha, hua⟩ := hu
  obtain ⟨b, hb, hsb⟩ := hs a ha
  refine ⟨b, hb, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul, hua,
    hsb, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

end Transvection

section OddCase

variable {h : UnitaryFieldData p f K} [CharP K 2]

@[expose] def oddMat₁ (ω : K) : Matrix (Fin 4) (Fin 4) K :=
  !![ω, 0, 0, 0; 0, ω, 0, 0; 0, 0, ω, 0; 0, 0, 0, 1]

@[expose] def oddMat₂ (ω : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, ω, 0; 0, 0, 0, ω ^ 2]

@[expose] def swapMat₁₃ : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1]

omit [CharP K 2] in
theorem swapMat₁₃_unitary :
    ((swapMat₁₃ : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * swapMat₁₃ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat₁₃, Matrix.mul_apply, Fin.sum_univ_four]

theorem det_swapMat₁₃ : (swapMat₁₃ : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [swapMat₁₃, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  grind

variable {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hbar : h.bar ω = ω ^ 2)

include hω hbar in
theorem oddMat₁_unitary : ((oddMat₁ ω).map h.bar)ᵀ * oddMat₁ ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oddMat₁, Matrix.mul_apply, Fin.sum_univ_four, hbar] <;>
    grind

include hω hbar in
theorem oddMat₂_unitary : ((oddMat₂ ω).map h.bar)ᵀ * oddMat₂ ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oddMat₂, Matrix.mul_apply, Fin.sum_univ_four, hbar] <;>
    grind

include hω in
theorem det_oddMat₁ : (oddMat₁ ω).det = 1 := by
  simp [oddMat₁, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  grind

include hω in
theorem det_oddMat₂ : (oddMat₂ ω).det = 1 := by
  simp [oddMat₂, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  grind

include hω hbar in
theorem hasLocalWitness_of_bar_eq_sq (hC : IsPrimeFormGram (1 : GL (Fin 4) K)) {φ : K ≃+* K}
    (hφω : φ ω = ω) : HasLocalWitness (primeFormFieldHom h hC φ) := by
  have hω1 : ω ≠ 1 := by
    rintro rfl
    grind
  set s₁ := suMk h (oddMat₁ ω) (oddMat₁_unitary hω hbar) (det_oddMat₁ hω)
  set s₂ := suMk h (oddMat₂ ω) (oddMat₂_unitary hω hbar) (det_oddMat₂ hω)
  set t := suMk h swapMat₁₃ swapMat₁₃_unitary det_swapMat₁₃
  have hcomm : ∀ a : K, oddMat₁ ω * transvMat a = transvMat a * oddMat₁ ω ∧
      oddMat₂ ω * transvMat a = transvMat a * oddMat₂ ω := fun a =>
    ⟨by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [oddMat₁, transvMat, Matrix.mul_apply, Fin.sum_univ_four] <;> grind,
    by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [oddMat₂, transvMat, Matrix.mul_apply, Fin.sum_univ_four]⟩
  refine hasLocalWitness_primeFormFieldHom_of hC φ (s₁ := s₁) (s₂ := s₂) (t := t) ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ isPGroup_transvGroup exists_mem_transvGroup_not_mem
    (fun u hu => conj_mem_transvGroup (fun a ha => ⟨a, ha, (hcomm a).1⟩) hu)
    (fun u hu => conj_mem_transvGroup (fun a ha => ⟨a, ha, (hcomm a).2⟩) hu)
    (fun u hu => primeFormFieldSU_mem_transvGroup hC φ hu)
  · refine gramSU_ext ?_
    rw [coe_primeFormFieldSU, coe_suMk]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [oddMat₁, hφω]
  · refine gramSU_ext ?_
    rw [coe_primeFormFieldSU, coe_suMk]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [oddMat₂, hφω]
  · refine gramSU_ext ?_
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_suMk, pow_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [oddMat₁, Matrix.mul_apply, Fin.sum_univ_four] <;> grind
  · refine gramSU_ext ?_
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_suMk, pow_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [oddMat₂, Matrix.mul_apply, Fin.sum_univ_four] <;> grind
  · refine gramSU_ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_suMk, coe_suMk]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [oddMat₁, oddMat₂, Matrix.mul_apply, Fin.sum_univ_four]
  · refine not_mem_normOneScalars_of_ne (i := 0) (j := 3) ?_
    rw [coe_suMk]
    simpa [oddMat₁] using hω1
  · refine gramSU_ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_suMk, coe_suMk]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [oddMat₁, swapMat₁₃, Matrix.mul_apply, Fin.sum_univ_four]
  · intro heq
    have h1 := congrArg (fun s : gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =>
      ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 2) heq
    simp only [Subgroup.coe_mul, Units.val_mul] at h1
    rw [coe_suMk, coe_suMk] at h1
    simp [oddMat₂, swapMat₁₃, Matrix.mul_apply, Fin.sum_univ_four] at h1
    exact hω1 h1

end OddCase

section EvenCase

variable {h : UnitaryFieldData p f K} [CharP K 2]

@[expose] def evenMat₁ (ω c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![ω ^ 2 + c, 1 + c, 0, 0; c, ω + c, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def evenMat₂ (ω c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, ω ^ 2 + c, 1 + c; 0, 0, c, ω + c]

@[expose] def swapMat₃₄ : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

omit [CharP K 2] in
theorem swapMat₃₄_unitary :
    ((swapMat₃₄ : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * swapMat₃₄ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat₃₄, Matrix.mul_apply, Fin.sum_univ_four]

theorem det_swapMat₃₄ : (swapMat₃₄ : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [swapMat₃₄, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  grind

variable {ω c : K} (hω : ω ^ 2 + ω + 1 = 0) (hbar : h.bar ω = ω) (hc : c + h.bar c = 1)

include hω hbar hc in
theorem evenMat₁_unitary : ((evenMat₁ ω c).map h.bar)ᵀ * evenMat₁ ω c = 1 := by
  have hc' : h.bar c = 1 + c := by grind
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evenMat₁, Matrix.mul_apply, Fin.sum_univ_four, hbar, hc'] <;> grind

include hω hbar hc in
theorem evenMat₂_unitary : ((evenMat₂ ω c).map h.bar)ᵀ * evenMat₂ ω c = 1 := by
  have hc' : h.bar c = 1 + c := by grind
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evenMat₂, Matrix.mul_apply, Fin.sum_univ_four, hbar, hc'] <;> grind

include hω in
theorem det_evenMat₁ : (evenMat₁ ω c).det = 1 := by
  simp [evenMat₁, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  grind

include hω in
theorem det_evenMat₂ : (evenMat₂ ω c).det = 1 := by
  simp [evenMat₂, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  grind

include hω hbar hc in
theorem hasLocalWitness_of_bar_eq_self (hC : IsPrimeFormGram (1 : GL (Fin 4) K))
    {φ : K ≃+* K} (hφω : φ ω = ω) (hφc : φ c = c) :
    HasLocalWitness (primeFormFieldHom h hC φ) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_add] at hc
    exact zero_ne_one hc
  set s₁ := suMk h (evenMat₁ ω c) (evenMat₁_unitary hω hbar hc) (det_evenMat₁ hω)
  set s₂ := suMk h (evenMat₂ ω c) (evenMat₂_unitary hω hbar hc) (det_evenMat₂ hω)
  set t := suMk h swapMat₃₄ swapMat₃₄_unitary det_swapMat₃₄
  have hconj₁ : ∀ a : K, evenMat₁ ω c * transvMat a = transvMat (ω ^ 2 * a) * evenMat₁ ω c :=
    fun a => by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [evenMat₁, transvMat, Matrix.mul_apply, Fin.sum_univ_four] <;> grind
  have hconj₂ : ∀ a : K, evenMat₂ ω c * transvMat a = transvMat a * evenMat₂ ω c := fun a => by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [evenMat₂, transvMat, Matrix.mul_apply, Fin.sum_univ_four]
  refine hasLocalWitness_primeFormFieldHom_of hC φ (s₁ := s₁) (s₂ := s₂) (t := t) ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ isPGroup_transvGroup exists_mem_transvGroup_not_mem
    (fun u hu => conj_mem_transvGroup (fun a ha => ⟨ω ^ 2 * a,
      by rw [map_mul, map_pow, hbar, ha], hconj₁ a⟩) hu)
    (fun u hu => conj_mem_transvGroup (fun a ha => ⟨a, ha, hconj₂ a⟩) hu)
    (fun u hu => primeFormFieldSU_mem_transvGroup hC φ hu)
  · refine gramSU_ext ?_
    rw [coe_primeFormFieldSU, coe_suMk]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [evenMat₁, hφω, hφc]
  · refine gramSU_ext ?_
    rw [coe_primeFormFieldSU, coe_suMk]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [evenMat₂, hφω, hφc]
  · refine gramSU_ext ?_
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_suMk, pow_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [evenMat₁, Matrix.mul_apply, Fin.sum_univ_four] <;> grind
  · refine gramSU_ext ?_
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_suMk, pow_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [evenMat₂, Matrix.mul_apply, Fin.sum_univ_four] <;> grind
  · refine gramSU_ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_suMk, coe_suMk]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [evenMat₁, evenMat₂, Matrix.mul_apply, Fin.sum_univ_four]
  · refine not_mem_normOneScalars_of_ne_zero (i := 1) (j := 0) (by decide) ?_
    rw [coe_suMk]
    simpa [evenMat₁] using hc0
  · refine gramSU_ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_suMk, coe_suMk]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [evenMat₁, swapMat₃₄, Matrix.mul_apply, Fin.sum_univ_four]
  · intro heq
    have h1 := congrArg (fun s : gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =>
      ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 2) heq
    simp only [Subgroup.coe_mul, Units.val_mul] at h1
    rw [coe_suMk, coe_suMk] at h1
    simp [evenMat₂, swapMat₃₄, Matrix.mul_apply, Fin.sum_univ_four] at h1

end EvenCase

theorem hasLocalWitness_primeFormFieldHom (h : UnitaryFieldData 2 f K)
    (hC : IsPrimeFormGram (1 : GL (Fin 4) K)) {φ : K ≃+* K} (hφ : φ ^ 3 = 1) :
    HasLocalWitness (primeFormFieldHom h hC φ) := by
  have := h.finite
  have : CharP K 2 := h.charP
  obtain ⟨ω, hω⟩ := WitnessG2.exists_orderOf_eq_three h.card
  have hω3 : (ω : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one, Units.val_one]
  have hω1 : (ω : K) ≠ 1 := by
    intro h1
    have h2 : ω = 1 := Units.ext h1
    rw [h2, orderOf_one] at hω
    omega
  have hq : (ω : K) ^ 2 + ω + 1 = 0 := by
    have h1 : ((ω : K) - 1) * ((ω : K) ^ 2 + ω + 1) = 0 := by linear_combination hω3
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd (sub_eq_zero.1 h2) hω1
    · exact h2
  have hφω : φ ω = ω := WitnessG2.ringEquiv_apply_eq_self hφ hω3
  have hbq : h.bar (ω : K) ^ 2 + h.bar ω + 1 = 0 := by
    rw [← map_pow, ← map_one h.bar, ← map_add, ← map_add, hq, map_zero]
  have hcases : h.bar (ω : K) = ω ∨ h.bar (ω : K) = ω ^ 2 := by
    have h1 : (h.bar (ω : K) - ω) * (h.bar (ω : K) + ω + 1) = 0 := by
      linear_combination hbq - hq
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl (sub_eq_zero.1 h2)
    · exact Or.inr (by linear_combination h2 - hq)
  rcases hcases with hbar | hbar
  · obtain ⟨c₀, hc₀⟩ := h.traceLin_surjective 1
    have hc₀' : c₀ + h.bar c₀ = 1 := by
      have h1 := congrArg Subtype.val hc₀
      simpa [UnitaryFieldData.trace] using h1
    have hφ3 : ∀ x, φ (φ (φ x)) = x := fun x => by
      have h1 := congrArg (fun τ : K ≃+* K => τ x) hφ
      simpa only [pow_succ, pow_zero, one_mul, RingAut.mul_apply, RingAut.one_apply] using h1
    refine hasLocalWitness_of_bar_eq_self (c := c₀ + φ c₀ + φ (φ c₀)) hq hbar ?_ hC hφω ?_
    · have e1 : h.bar (φ c₀) = φ (h.bar c₀) := (map_bar_comm h φ c₀).symm
      have e2 : h.bar (φ (φ c₀)) = φ (φ (h.bar c₀)) := by
        rw [← map_bar_comm h φ, ← map_bar_comm h φ]
      have h1 : φ c₀ + φ (h.bar c₀) = 1 := by rw [← map_add, hc₀', map_one]
      have h2 : φ (φ c₀) + φ (φ (h.bar c₀)) = 1 := by
        rw [← map_add, ← map_add, hc₀', map_one, map_one]
      rw [map_add, map_add, e1, e2]
      grind
    · rw [map_add, map_add, hφ3]
      ring
  · exact hasLocalWitness_of_bar_eq_sq hq hbar hC hφω

end CFSG.RankThree.PartTwo.Sec4.WitnessU4

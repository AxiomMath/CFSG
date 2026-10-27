module

public import CFSG.Quasithin.Background.A318PL3Lin
public import CFSG.RankThree.PartTwo.KFacts.AutPSUOrderThree
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.Quasithin

namespace A318P

open Matrix
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner inner_map_congr)

variable {p f : ℕ} {K : Type} [Field K]

theorem bar_mul_self_of_cube (h : UnitaryFieldData p f K) (hq : 3 ∣ p ^ f + 1) {ω : K}
    (hω : ω ^ 3 = 1) : h.bar ω * ω = 1 := by
  obtain ⟨m, hm⟩ := hq
  rw [UnitaryFieldData.bar_apply, ← pow_succ, hm, pow_mul, hω, one_pow]

theorem heisA_unitary (h : UnitaryFieldData p f K) (hq : 3 ∣ p ^ f + 1) {ω : K} (hω : ω ^ 3 = 1) :
    ((heisA ω : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * heisA ω = 1 := by
  have h1 := bar_mul_self_of_cube h hq hω
  have h2 : h.bar (ω ^ 2) * ω ^ 2 = 1 := by
    rw [map_pow, ← mul_pow, h1, one_pow]
  rw [heisA, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i
  · simp
  · simpa using h1
  · simpa using h2

theorem heisB_unitary (h : UnitaryFieldData p f K) :
    ((heisB : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * heisB = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisB, Matrix.mul_apply, Fin.sum_univ_three]

theorem heisASL_toGL_mem (h : UnitaryFieldData p f K) (hq : 3 ∣ p ^ f + 1) {ω : K}
    (hω : ω ^ 3 = 1) : SpecialLinearGroup.toGL (heisASL ω hω) ∈ unitarySU p f K 3 := by
  rw [mem_unitarySU_iff h]
  refine ⟨?_, heisA_unitary h hq hω⟩
  exact (heisASL ω hω).det_coe

theorem heisBSL_toGL_mem (h : UnitaryFieldData p f K) :
    SpecialLinearGroup.toGL (heisBSL : SpecialLinearGroup (Fin 3) K) ∈ unitarySU p f K 3 := by
  rw [mem_unitarySU_iff h]
  exact ⟨(heisBSL : SpecialLinearGroup (Fin 3) K).det_coe, heisB_unitary h⟩

theorem toGL_scalarElement {u : Kˣ} (hu : u ^ 3 = 1) :
    SpecialLinearGroup.toGL (LinearFlag.scalarElement u hu) =
      GeneralLinearGroup.scalar (Fin 3) u := by
  apply Units.ext
  change ((LinearFlag.scalarElement u hu : SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) = _
  rw [LinearFlag.coe_scalarElement, GeneralLinearGroup.coe_scalar]

theorem scalar_toGL_mem (h : UnitaryFieldData p f K) (hq : 3 ∣ p ^ f + 1) {ω : K} (hω : ω ^ 3 = 1)
    (hω0 : ω ≠ 0) :
    (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ω hω0) : GL (Fin 3) K) ∈ unitarySU p f K 3 := by
  rw [mem_unitarySU_iff h]
  have h1 := bar_mul_self_of_cube h hq hω
  refine ⟨?_, ?_⟩
  · rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Units.val_mk0, hω]
  · rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_map (map_zero h.bar),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    simpa using h1

theorem exists_nine_psu (h : UnitaryFieldData p f K) (hq : 3 ∣ p ^ f + 1) {ω : K} (hω : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (σ : K ≃+* K) (hσ : σ ω = ω) :
    ∃ E : Subgroup (unitaryPSU h 3), Nat.card E = 9 ∧ (∀ a b : E, a * b = b * a) ∧
      (∀ x ∈ E, x ^ 3 = 1) ∧ ∀ y ∈ E, psuField h σ y = y := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  let A : unitarySU p f K 3 := ⟨SpecialLinearGroup.toGL (heisASL ω hω), heisASL_toGL_mem h hq hω⟩
  let B : unitarySU p f K 3 := ⟨SpecialLinearGroup.toGL (heisBSL : SpecialLinearGroup (Fin 3) K),
    heisBSL_toGL_mem h⟩
  let Z : unitarySU p f K 3 :=
    ⟨GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ω hω0), scalar_toGL_mem h hq hω hω0⟩
  have hZ : unitaryProj h 3 Z = 1 := by
    rw [← MonoidHom.mem_ker, ker_unitaryProj]
    have h1 := bar_mul_self_of_cube h hq hω
    refine ⟨Units.mk0 ω hω0, ?_, ?_, rfl⟩
    · change ω * h.bar ω = 1
      rw [mul_comm]
      exact h1
    · apply Units.ext
      simpa using hω
  have hA3 : A ^ 3 = 1 := by
    apply Subtype.ext
    change (SpecialLinearGroup.toGL (heisASL ω hω)) ^ 3 = 1
    rw [← map_pow, heisASL_pow_three, map_one]
  have hB3 : B ^ 3 = 1 := by
    apply Subtype.ext
    change (SpecialLinearGroup.toGL (heisBSL : SpecialLinearGroup (Fin 3) K)) ^ 3 = 1
    rw [← map_pow, heisBSL_pow_three, map_one]
  have hAB : A * B = Z * (B * A) := by
    apply Subtype.ext
    change SpecialLinearGroup.toGL (heisASL ω hω) *
        SpecialLinearGroup.toGL (heisBSL : SpecialLinearGroup (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ω hω0) *
        (SpecialLinearGroup.toGL (heisBSL : SpecialLinearGroup (Fin 3) K) *
          SpecialLinearGroup.toGL (heisASL ω hω))
    rw [← map_mul, ← map_mul, heisASL_mul_heisBSL hω hω0, map_mul, toGL_scalarElement]
  have hu : unitaryProj h 3 A ^ 3 = 1 := by rw [← map_pow, hA3, map_one]
  have hv : unitaryProj h 3 B ^ 3 = 1 := by rw [← map_pow, hB3, map_one]
  have hcomm : unitaryProj h 3 A * unitaryProj h 3 B = unitaryProj h 3 B * unitaryProj h 3 A := by
    rw [← map_mul, ← map_mul, hAB, map_mul, hZ, one_mul]
  have hind : ∀ i j : ℕ, unitaryProj h 3 A ^ i * unitaryProj h 3 B ^ j = 1 → 3 ∣ i ∧ 3 ∣ j := by
    intro i j hij
    rw [← map_pow, ← map_pow, ← map_mul, ← MonoidHom.mem_ker, ker_unitaryProj] at hij
    obtain ⟨c, -, -, hc⟩ := hij
    refine heis_indep hω hω1 i j (c : K) ?_
    have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h1
    have h2 : ((A ^ i * B ^ j : unitarySU p f K 3) : GL (Fin 3) K) =
        SpecialLinearGroup.toGL (heisASL ω hω ^ i * (heisBSL : SpecialLinearGroup (Fin 3) K) ^ j) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, map_mul, map_pow]
      rfl
    rw [h2] at h1
    have h3 : ((SpecialLinearGroup.toGL (heisASL ω hω ^ i *
        (heisBSL : SpecialLinearGroup (Fin 3) K) ^ j) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        heisA ω ^ i * (heisB : Matrix (Fin 3) (Fin 3) K) ^ j := by
      change (((heisASL ω hω ^ i * (heisBSL : SpecialLinearGroup (Fin 3) K) ^ j :
        SpecialLinearGroup (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) = _
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
        Matrix.SpecialLinearGroup.coe_pow]
      rfl
    rw [h3] at h1
    rw [h1, Matrix.scalar_apply]
  obtain ⟨E, hE9, hEc, hE3, hEfix⟩ := exists_nine_of_commuting hu hv hcomm hind
  refine ⟨E, hE9, hEc, hE3, fun y hy => ?_⟩
  refine hEfix (psuField h σ : unitaryPSU h 3 →* unitaryPSU h 3) ?_ ?_ y hy
  · change psuField h σ (unitaryProj h 3 A) = unitaryProj h 3 A
    rw [show unitaryProj h 3 A = ((A : unitarySU p f K 3) : unitaryPSU h 3) from rfl, psuField_mk]
    congr 1
    apply Subtype.ext
    rw [coe_suField]
    apply Units.ext
    rw [coe_glAut]
    change (heisA ω).map σ = heisA ω
    rw [heisA, Matrix.diagonal_map (map_zero σ)]
    congr 1
    ext a
    fin_cases a <;> simp [hσ]
  · change psuField h σ (unitaryProj h 3 B) = unitaryProj h 3 B
    rw [show unitaryProj h 3 B = ((B : unitarySU p f K 3) : unitaryPSU h 3) from rfl, psuField_mk]
    congr 1
    apply Subtype.ext
    rw [coe_suField]
    apply Units.ext
    rw [coe_glAut]
    change (heisB : Matrix (Fin 3) (Fin 3) K).map σ = heisB
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heisB]

theorem map_psuConj_range (h : UnitaryFieldData p f K) :
    (psuConj h).range.map (MulAut.congr (psuPrimeFormEquiv h)).toMonoidHom =
      UnitaryHigher.primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  ext α
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨⟨A, mem_primeFormUnitary_one A.2⟩, (congr_psuConj A).symm⟩
  · rintro ⟨B, rfl⟩
    have hB : (B : GL (Fin 3) K) ∈ unitaryIsom3 h := by
      have h1 := UnitaryHigher.mem_primeFormUnitary.1 B.2
      rw [mem_unitaryIsom3]
      simpa [Units.val_one] using h1
    refine ⟨psuConj h ⟨B, hB⟩, ⟨⟨B, hB⟩, rfl⟩, ?_⟩
    exact congr_psuConj (h := h) ⟨B, hB⟩

theorem relIndex_inner_psuConj_eq_three (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (h3 : 3 ∣ p ^ f + 1) :
    (inner (unitaryPSU h 3)).relIndex (psuConj h).range = 3 := by
  have := h.finite
  have h1 := Subgroup.relIndex_map_map_of_injective
    (f := (MulAut.congr (psuPrimeFormEquiv h)).toMonoidHom) (inner (unitaryPSU h 3))
    (psuConj h).range (MulAut.congr (psuPrimeFormEquiv h)).injective
  rw [inner_map_congr, map_psuConj_range h] at h1
  rw [← h1]
  obtain ⟨-, -, hcard, -⟩ := UnitaryHigher.unitary_full_diagonal_outer_order h (le_refl 3)
    (fun ⟨_, h2⟩ => by omega)
  rw [Subgroup.relIndex, Subgroup.index_eq_card, hcard, Nat.gcd_eq_left h3]

theorem three_dvd_card_sub_one_of_unitary (h : UnitaryFieldData p f K) (h3 : 3 ∣ p ^ f + 1)
    (hq : 2 < p ^ f) : 3 ∣ Nat.card K - 1 := by
  rw [h.card, pow_mul']
  obtain ⟨m, hm⟩ := h3
  have hq1 : 1 ≤ p ^ f := by omega
  have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
  refine ⟨m * (p ^ f - 1), ?_⟩
  zify [hq1, hq2]
  have hm' : (p ^ f : ℤ) + 1 = 3 * m := by exact_mod_cast hm
  linear_combination ((p ^ f : ℤ) - 1) * hm'

@[expose] noncomputable def l3FramePSU (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) (h3 : 3 ∣ p ^ f + 1) :
    L3Frame (unitaryPSU h 3) (K ≃+* K) where
  D := (psuConj h).range
  fld := psuField h
  inner_le := (stdPinnedPSU3 h).inn_le
  fld_norm := fun σ d hd => by
    obtain ⟨A, rfl⟩ := hd
    rw [psuField_mul_psuConj_mul_inv]
    exact ⟨_, rfl⟩
  fld_inter := fun σ hσ => psuField_mem_range_psuConj_iff.1 hσ
  three_mem := fun α k _ => by
    obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
    exact ⟨psuConj h A, ⟨A, rfl⟩, σ, rfl⟩
  card_DI := relIndex_inner_psuConj_eq_three h hq h3
  lang := fun α hα _ hαD => by
    obtain ⟨σ, hσ, H, rfl⟩ := unitary_order_three_field_descent hq α hα hαD
    exact ⟨psuConj h H, ⟨H, rfl⟩, σ, hσ, rfl⟩
  nine := fun c hc => by
    have := h.finite
    obtain ⟨ω, hω, hω1⟩ := exists_cube_root_of_unity (K := K)
      (three_dvd_card_sub_one_of_unitary h h3 hq)
    have hσ3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
    obtain ⟨E, hE9, hEc, hE3, hEfix⟩ :=
      exists_nine_psu h h3 hω hω1 c (ringEquiv_fix_cube_root hσ3 hω hω1)
    exact ⟨E, hE9, ⟨⟨⟨fun a b => hEc a b⟩⟩, hE3⟩, hEfix⟩

end A318P

end CFSG.Quasithin

module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open Matrix

section Frob

variable {K : Type} [Field K]

theorem frobGL_one_apply (A : GL (Fin 3) K) : frobGL (1 : K ≃+* K) A = A := by
  apply Units.ext
  rw [coe_frobGL]
  ext i j
  rfl

theorem frobGL_mul_apply (σ τ : K ≃+* K) (A : GL (Fin 3) K) :
    frobGL (σ * τ) A = frobGL σ (frobGL τ A) := by
  apply Units.ext
  rw [coe_frobGL, coe_frobGL, coe_frobGL]
  ext i j
  rfl

theorem trace_frobGL (σ : K ≃+* K) (A : GL (Fin 3) K) :
    ((frobGL σ A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      σ ((A : Matrix (Fin 3) (Fin 3) K).trace) := by
  rw [coe_frobGL, AddMonoidHom.map_trace σ]

theorem trace_conj_gl (H A : GL (Fin 3) K) :
    ((H * A * H⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      (A : Matrix (Fin 3) (Fin 3) K).trace := by
  rw [Units.val_mul, Units.val_mul]
  exact Matrix.trace_units_conj H _

theorem trace_conj_gl' (H A : GL (Fin 3) K) :
    ((H⁻¹ * A * H : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      (A : Matrix (Fin 3) (Fin 3) K).trace := by
  have h := trace_conj_gl H⁻¹ A
  rwa [inv_inv] at h

theorem coe_torusHom_inv (μ : Kˣ) :
    ((torusHom (μ, μ⁻¹) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(μ : K), (μ : K)⁻¹, 1] := by
  rw [coe_torusHom]
  congr 1
  funext i
  fin_cases i <;> simp

theorem trace_torusHom_inv (μ : Kˣ) :
    ((torusHom (μ, μ⁻¹) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      (μ : K) + (μ : K)⁻¹ + 1 := by
  rw [coe_torusHom_inv, trace_diagonal, Fin.sum_univ_three]
  rfl

theorem ringAut_fixed_of_add_inv {σ : K ≃+* K} (hσ : ∀ c, σ (σ (σ c)) = c) {μ : K}
    (hμ0 : μ ≠ 0) (hμ2 : μ ^ 2 ≠ 1) (h : σ (μ + μ⁻¹) = μ + μ⁻¹) : σ μ = μ := by
  have hν0 : σ μ ≠ 0 := (map_ne_zero σ).mpr hμ0
  have h1 : σ μ + (σ μ)⁻¹ = μ + μ⁻¹ := by rw [← h, map_add, map_inv₀]
  have hμi : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ0
  have hνi : σ μ * (σ μ)⁻¹ = 1 := mul_inv_cancel₀ hν0
  have h2 : (σ μ - μ) * (σ μ - μ⁻¹) = 0 := by
    linear_combination σ μ * h1 + hμi - hνi
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exfalso
    have h4 : σ μ = μ⁻¹ := sub_eq_zero.mp h3
    have h5 : σ (σ μ) = μ := by rw [h4, map_inv₀, h4, inv_inv]
    have h6 : μ = μ⁻¹ := by
      have := hσ μ
      rw [h5, h4] at this
      exact this.symm
    apply hμ2
    rw [sq]
    nth_rewrite 2 [h6]
    exact hμi

end Frob

section Semi

variable {π : Bool} {q : ℕ} {K : Type} [Field K]

@[expose] def SemiAct (ζ : MulAut (slPi π 3 q K)) (τ : K ≃+* K) (g : GL (Fin 3) K) : Prop :=
  ∀ s : slPi π 3 q K, ((ζ s : slPi π 3 q K) : GL (Fin 3) K) = g * frobGL τ s * g⁻¹

theorem SemiAct.mul {ζ ζ' : MulAut (slPi π 3 q K)} {τ τ' : K ≃+* K} {g g' : GL (Fin 3) K}
    (h : SemiAct ζ τ g) (h' : SemiAct ζ' τ' g') :
    SemiAct (ζ * ζ') (τ * τ') (g * frobGL τ g') := by
  intro s
  rw [MulAut.mul_apply, h, h', map_mul, map_mul, map_inv, frobGL_mul_apply]
  group

theorem semiAct_one : SemiAct (1 : MulAut (slPi π 3 q K)) 1 1 := by
  intro s
  rw [frobGL_one_apply, MulAut.one_apply, one_mul, inv_one, mul_one]

theorem SemiAct.pow {ζ : MulAut (slPi π 3 q K)} {τ : K ≃+* K} {g : GL (Fin 3) K}
    (h : SemiAct ζ τ g) (k : ℕ) : ∃ g' : GL (Fin 3) K, SemiAct (ζ ^ k) (τ ^ k) g' := by
  induction k with
  | zero => exact ⟨1, by rw [pow_zero, pow_zero]; exact semiAct_one⟩
  | succ k ih =>
    obtain ⟨g', hg'⟩ := ih
    exact ⟨_, by rw [pow_succ, pow_succ]; exact hg'.mul h⟩

theorem semiAct_one_iff {ζ : MulAut (slPi π 3 q K)} {g : GL (Fin 3) K} :
    SemiAct ζ 1 g ↔
      ∀ s : slPi π 3 q K, ((ζ s : slPi π 3 q K) : GL (Fin 3) K) = g * s * g⁻¹ := by
  simp only [SemiAct, frobGL_one_apply]

theorem semiAct_of_conj_frob {ζ : MulAut (slPi π 3 q K)} {σ : K ≃+* K} {H : GL (Fin 3) K}
    (h : ∀ s : slPi π 3 q K,
      ((ζ s : slPi π 3 q K) : GL (Fin 3) K) = H * frobGL σ (H⁻¹ * s * H) * H⁻¹) :
    SemiAct ζ σ (H * frobGL σ H⁻¹) := fun s => by rw [h, conj_frobGL_conj]

theorem trace_fixed_of_field {ζ : MulAut (slPi π 3 q K)} {σ : K ≃+* K} {H : GL (Fin 3) K}
    (hζ : ∀ s : slPi π 3 q K,
      ((ζ s : slPi π 3 q K) : GL (Fin 3) K) = H * frobGL σ (H⁻¹ * s * H) * H⁻¹)
    {s : slPi π 3 q K} (hs : ζ s = s) :
    σ ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace := by
  have e := congrArg (fun x : slPi π 3 q K => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace)
    hs
  rwa [hζ s, trace_conj_gl, trace_frobGL, trace_conj_gl'] at e

theorem eq_smul_one_of_commute_diagonal {d₀ d₁ d₂ : K} (h01 : d₀ ≠ d₁) (h02 : d₀ ≠ d₂)
    (h12 : d₁ ≠ d₂) {M : Matrix (Fin 3) (Fin 3) K}
    (h1 : M * diagonal ![d₀, d₁, d₂] = diagonal ![d₀, d₁, d₂] * M)
    (h2 : M * ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M) :
    M = M 0 0 • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have m01 : M 0 1 = 0 :=
    entry_eq_zero_of_commute_diagonal h1 (i := 0) (j := 1) (by simpa using h01)
  have m02 : M 0 2 = 0 :=
    entry_eq_zero_of_commute_diagonal h1 (i := 0) (j := 2) (by simpa using h02)
  have m12 : M 1 2 = 0 :=
    entry_eq_zero_of_commute_diagonal h1 (i := 1) (j := 2) (by simpa using h12)
  have m10 : M 1 0 = 0 :=
    entry_eq_zero_of_commute_diagonal h1 (i := 1) (j := 0) (by simpa using h01.symm)
  have m20 : M 2 0 = 0 :=
    entry_eq_zero_of_commute_diagonal h1 (i := 2) (j := 0) (by simpa using h02.symm)
  have m21 : M 2 1 = 0 :=
    entry_eq_zero_of_commute_diagonal h1 (i := 2) (j := 1) (by simpa using h12.symm)
  rw [coe_cycThree] at h2
  have c02 := congrFun (congrFun h2 0) 2
  have c10 := congrFun (congrFun h2 1) 0
  simp [mul_apply, Fin.sum_univ_three] at c02 c10
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m01, m02, m10, m12, m20, m21, c02, c10]

theorem eq_one_of_semiAct_one_of_fixed {ζ : MulAut (slPi π 3 q K)} {g : GL (Fin 3) K}
    (hζ : SemiAct ζ 1 g) {μ : Kˣ} (hμ1 : μ ≠ 1) (hμ2 : μ ^ 2 ≠ 1) (h : GL (Fin 3) K)
    {s₁ s₂ : slPi π 3 q K} (hs₁ : (s₁ : GL (Fin 3) K) = h * torusHom (μ, μ⁻¹) * h⁻¹)
    (hs₂ : (s₂ : GL (Fin 3) K) = h * cycThree * h⁻¹) (h1 : ζ s₁ = s₁) (h2 : ζ s₂ = s₂) :
    ζ = 1 := by
  rw [semiAct_one_iff] at hζ
  obtain ⟨M, hM⟩ : ∃ M : GL (Fin 3) K, M = h⁻¹ * g * h := ⟨_, rfl⟩
  have key : ∀ (s : slPi π 3 q K) (d : GL (Fin 3) K), (s : GL (Fin 3) K) = h * d * h⁻¹ →
      ζ s = s → M * d = d * M := by
    intro s d hs hfix
    have e1 := hζ s
    rw [hfix, hs] at e1
    rw [hM]
    calc h⁻¹ * g * h * d = h⁻¹ * (g * (h * d * h⁻¹) * g⁻¹) * g * h := by group
      _ = h⁻¹ * (h * d * h⁻¹) * g * h := by rw [← e1]
      _ = d * (h⁻¹ * g * h) := by group
  have k1 := congrArg Units.val (key s₁ _ hs₁ h1)
  have k2 := congrArg Units.val (key s₂ _ hs₂ h2)
  rw [Units.val_mul, Units.val_mul, coe_torusHom_inv] at k1
  rw [Units.val_mul, Units.val_mul] at k2
  have hμK : (μ : K) ≠ 1 := fun h' => hμ1 (Units.ext h')
  have hμ0 : (μ : K) ≠ 0 := μ.ne_zero
  have hμK2 : (μ : K) ^ 2 ≠ 1 := fun h' => hμ2 (Units.ext (by rw [Units.val_pow_eq_pow_val, h',
    Units.val_one]))
  have d01 : (μ : K) ≠ (μ : K)⁻¹ := by
    intro h'
    apply hμK2
    rw [sq]
    nth_rewrite 2 [h']
    exact mul_inv_cancel₀ hμ0
  have d12 : (μ : K)⁻¹ ≠ 1 := fun h' => hμK (inv_eq_one.mp h')
  obtain ⟨c, hc⟩ : ∃ c : K, (M : Matrix (Fin 3) (Fin 3) K) = c • 1 :=
    ⟨_, eq_smul_one_of_commute_diagonal d01 hμK d12 k1 k2⟩
  have hgM : (g : Matrix (Fin 3) (Fin 3) K) = c • 1 := by
    have hg : g = h * M * h⁻¹ := by rw [hM]; group
    rw [hg, Units.val_mul, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgc : ∀ x : GL (Fin 3) K, g * x = x * g := by
    intro x
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hgM, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  refine MulEquiv.ext fun s => Subtype.ext ?_
  rw [hζ s, MulAut.one_apply, hgc, mul_inv_cancel_right]

end Semi

section Linear

variable {K : Type} [Field K]

theorem eq_of_descendAut_eq {β γ : MulAut (SpecialLinearGroup (Fin 3) K)}
    (h : descendAut 3 K β = descendAut 3 K γ) : β = γ := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  apply mulAut_eq_of_inv_mul_mem_center
  intro g
  rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one,
    ← descendAut_proj, ← descendAut_proj, h]

theorem exists_eq_slConjugation_of_descendAut_mem {β : MulAut (SpecialLinearGroup (Fin 3) K)}
    (hD : descendAut 3 K β ∈ linearAutGroup 3 K) :
    ∃ A : GL (Fin 3) K, β = slConjugation 3 K A := by
  rw [linearAutGroup_eq_range] at hD
  obtain ⟨A, hA⟩ := hD
  exact ⟨A, eq_of_descendAut_eq hA.symm⟩

theorem exists_conj_of_descendAut_mem {q : ℕ} {ζ : MulAut (slPi true 3 q K)}
    (hD : descendAut 3 K (MulAut.congr (slPiTrueEquiv q K) ζ) ∈ linearAutGroup 3 K) :
    ∃ y : GL (Fin 3) K, SemiAct ζ 1 y := by
  obtain ⟨A, hA⟩ := exists_eq_slConjugation_of_descendAut_mem hD
  refine ⟨A, semiAct_one_iff.mpr fun s => ?_⟩
  have h1 : MulAut.congr (slPiTrueEquiv q K) ζ (slPiTrueEquiv q K s) =
      slPiTrueEquiv q K (ζ s) := by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  rw [← toGL_slPiTrueEquiv (ζ s), ← h1, hA, toGL_slConjugation, toGL_slPiTrueEquiv]

theorem exists_field_of_descendAut_not_mem [Finite K] {q : ℕ} {ζ : MulAut (slPi true 3 q K)}
    (hζ : ζ ^ 3 = 1)
    (hD : descendAut 3 K (MulAut.congr (slPiTrueEquiv q K) ζ) ∉ linearAutGroup 3 K) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧ ∃ H : GL (Fin 3) K, ∀ s : slPi true 3 q K,
      ((ζ s : slPi true 3 q K) : GL (Fin 3) K) = H * frobGL σ (H⁻¹ * s * H) * H⁻¹ := by
  have hα3 : descendAut 3 K (MulAut.congr (slPiTrueEquiv q K) ζ) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, hζ, map_one, map_one]
  obtain ⟨σ, hσ3, H, hαH⟩ := linear_order_three_field_descent le_rfl _ hα3 hD
  have hβ : MulAut.congr (slPiTrueEquiv q K) ζ =
      slConjugation 3 K H * slFieldAut (Fin 3) K σ * (slConjugation 3 K H)⁻¹ :=
    eq_of_descendAut_eq (by rw [hαH, map_mul, map_mul, map_inv]; rfl)
  refine ⟨σ, hσ3, H, fun s => ?_⟩
  have h1 : MulAut.congr (slPiTrueEquiv q K) ζ (slPiTrueEquiv q K s) =
      slPiTrueEquiv q K (ζ s) := by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  rw [← toGL_slPiTrueEquiv (ζ s), ← h1, hβ, MulAut.mul_apply, MulAut.mul_apply,
    toGL_slConjugation, toGL_slFieldAut, ← map_inv, toGL_slConjugation, toGL_slPiTrueEquiv,
    inv_inv]

end Linear

section Unitary

variable {p f : ℕ} {K : Type} [Field K]

theorem eq_of_centerDescend_eq (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f)
    {β γ : MulAut (unitarySU p f K 3)}
    (hβγ : MulAut.congr (suCenterEquiv h hq2) (centerDescend _ β) =
      MulAut.congr (suCenterEquiv h hq2) (centerDescend _ γ)) : β = γ := by
  have : Group.IsPerfect (unitarySU p f K 3) := isPerfect_unitarySU_three h hq2
  have hγ' : centerDescend _ β = centerDescend _ γ := (MulAut.congr _).injective hβγ
  apply mulAut_eq_of_inv_mul_mem_center
  intro g
  have h1 := congrArg (fun τ : MulAut (unitarySU p f K 3 ⧸ Subgroup.center _) =>
    τ (g : unitarySU p f K 3 ⧸ Subgroup.center _)) hγ'
  simp only [centerDescend_mk] at h1
  exact QuotientGroup.eq.mp h1.symm

theorem exists_conj_of_psuConj_mem (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f)
    {ζ : MulAut (slPi false 3 (p ^ f) K)}
    (hD : MulAut.congr (suCenterEquiv h hq2)
      (centerDescend _ (MulAut.congr (slPiFalseEquiv p f K) ζ)) ∈ (psuConj h).range) :
    ∃ y ∈ glPi false 3 (p ^ f) K, SemiAct ζ 1 y := by
  obtain ⟨A, hA⟩ := hD
  have hβA : MulAut.congr (slPiFalseEquiv p f K) ζ = suConj h A :=
    eq_of_centerDescend_eq h hq2 (by rw [congr_centerDescend_suConj, hA])
  refine ⟨A, (mem_glPi_false h).mpr (mem_unitaryIsom3.mp A.2), semiAct_one_iff.mpr fun s => ?_⟩
  have h1 : MulAut.congr (slPiFalseEquiv p f K) ζ (slPiFalseEquiv p f K s) =
      slPiFalseEquiv p f K (ζ s) := by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  rw [← coe_slPiFalseEquiv (ζ s), ← h1, hβA, coe_suConj, coe_slPiFalseEquiv]
  rfl

theorem exists_field_of_psuConj_not_mem (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f)
    {ζ : MulAut (slPi false 3 (p ^ f) K)} (hζ : ζ ^ 3 = 1)
    (hD : MulAut.congr (suCenterEquiv h hq2)
      (centerDescend _ (MulAut.congr (slPiFalseEquiv p f K) ζ)) ∉ (psuConj h).range) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧ ∃ H ∈ glPi false 3 (p ^ f) K, ∀ s : slPi false 3 (p ^ f) K,
      ((ζ s : slPi false 3 (p ^ f) K) : GL (Fin 3) K) = H * frobGL σ (H⁻¹ * s * H) * H⁻¹ := by
  have hα3 : MulAut.congr (suCenterEquiv h hq2)
      (centerDescend _ (MulAut.congr (slPiFalseEquiv p f K) ζ)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, ← map_pow, hζ, map_one, map_one, map_one]
  obtain ⟨σ, hσ3, H, hαH⟩ := unitary_order_three_field_descent hq2 _ hα3 hD
  have hβ : MulAut.congr (slPiFalseEquiv p f K) ζ =
      suConj h H * suField h σ * (suConj h H)⁻¹ :=
    eq_of_centerDescend_eq h hq2 (by
      rw [hαH, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, congr_centerDescend_suConj,
        congr_centerDescend_suField])
  refine ⟨σ, hσ3, H, (mem_glPi_false h).mpr (mem_unitaryIsom3.mp H.2), fun s => ?_⟩
  have h1 : MulAut.congr (slPiFalseEquiv p f K) ζ (slPiFalseEquiv p f K s) =
      slPiFalseEquiv p f K (ζ s) := by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  rw [← coe_slPiFalseEquiv (ζ s), ← h1, hβ, MulAut.mul_apply, MulAut.mul_apply, coe_suConj,
    coe_suField, ← map_inv, coe_suConj, glAut_eq_frobGL, coe_slPiFalseEquiv]
  simp only [Subgroup.coe_inv, inv_inv]

end Unitary

section Dichotomy

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem exists_conj_or_field_of_pow_three_eq_one (hK : PiField π p f K) (hq2 : 2 < p ^ f)
    {ζ : MulAut (slPi π 3 (p ^ f) K)} (hζ : ζ ^ 3 = 1) :
    (∃ y ∈ glPi π 3 (p ^ f) K, SemiAct ζ 1 y) ∨
      ∃ σ : K ≃+* K, orderOf σ = 3 ∧ ∃ H ∈ glPi π 3 (p ^ f) K, ∀ s : slPi π 3 (p ^ f) K,
        ((ζ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = H * frobGL σ (H⁻¹ * s * H) * H⁻¹ := by
  have := hK.finite
  cases π
  · have h := hK.unitary
    by_cases hD : MulAut.congr (suCenterEquiv h hq2)
        (centerDescend _ (MulAut.congr (slPiFalseEquiv p f K) ζ)) ∈ (psuConj h).range
    · exact Or.inl (exists_conj_of_psuConj_mem h hq2 hD)
    · exact Or.inr (exists_field_of_psuConj_not_mem h hq2 hζ hD)
  · by_cases hD : descendAut 3 K (MulAut.congr (slPiTrueEquiv (p ^ f) K) ζ) ∈ linearAutGroup 3 K
    · obtain ⟨y, hy⟩ := exists_conj_of_descendAut_mem hD
      exact Or.inl ⟨y, mem_glPi_true _ _, hy⟩
    · obtain ⟨σ, hσ, H, hH⟩ := exists_field_of_descendAut_not_mem hζ hD
      exact Or.inr ⟨σ, hσ, H, mem_glPi_true _ _, hH⟩

theorem exists_semiAct_of_pow_three_eq_one (hK : PiField π p f K) (hq2 : 2 < p ^ f)
    {ζ : MulAut (slPi π 3 (p ^ f) K)} (hζ : ζ ^ 3 = 1) :
    ∃ τ : K ≃+* K, (τ = 1 ∨ orderOf τ = 3) ∧ ∃ g : GL (Fin 3) K, SemiAct ζ τ g := by
  rcases exists_conj_or_field_of_pow_three_eq_one hK hq2 hζ with ⟨y, -, hy⟩ | ⟨σ, hσ, H, -, hH⟩
  · exact ⟨1, Or.inl rfl, y, hy⟩
  · exact ⟨σ, Or.inr hσ, _, semiAct_of_conj_frob hH⟩

end Dichotomy

section PGroups

variable {K : Type} [Field K]

theorem cycThree_mul_torusHom (a b : Kˣ) :
    cycThree * torusHom (a, b) = torusHom ((a * b)⁻¹, a) * cycThree := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_torusHom, coe_torusHom, coe_cycThree]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, diagonal]

theorem torusHom_mul_cycThree (a b : Kˣ) :
    torusHom (a, b) * cycThree = cycThree * torusHom (b, (a * b)⁻¹) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_torusHom, coe_torusHom, coe_cycThree]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, diagonal]

@[expose] def torusPow (μ : Kˣ) : Subgroup (GL (Fin 3) K) :=
  ((Subgroup.zpowers μ).prod (Subgroup.zpowers μ)).map torusHom

theorem mem_torusPow {μ a b : Kˣ} (ha : a ∈ Subgroup.zpowers μ)
    (hb : b ∈ Subgroup.zpowers μ) : torusHom (a, b) ∈ torusPow μ :=
  ⟨(a, b), Subgroup.mem_prod.mpr ⟨ha, hb⟩, rfl⟩

theorem pow_eq_one_of_mem_zpowers {G : Type*} [Group G] {μ x : G} {k : ℕ} (hμ : μ ^ k = 1)
    (hx : x ∈ Subgroup.zpowers μ) : x ^ k = 1 := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hμ,
    _root_.one_zpow]

theorem isPGroup_torusPow {μ : Kˣ} {k : ℕ} (hμ : μ ^ 3 ^ k = 1) :
    IsPGroup 3 (torusPow μ) := by
  apply IsPGroup.map
  rintro ⟨⟨x, y⟩, hxy⟩
  obtain ⟨hx, hy⟩ := Subgroup.mem_prod.mp hxy
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, Prod.pow_mk]
  rw [pow_eq_one_of_mem_zpowers hμ hx, pow_eq_one_of_mem_zpowers hμ hy]
  rfl

theorem cycThree_mem_normalizer_torusPow (μ : Kˣ) :
    cycThree ∈ Subgroup.normalizer (torusPow μ : Set (GL (Fin 3) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    obtain ⟨ha, hb⟩ := Subgroup.mem_prod.mp hab
    have h := mem_torusPow (inv_mem (mul_mem ha hb)) ha
    rwa [← mul_inv_cancel_right (torusHom ((a * b)⁻¹, a)) cycThree, ← cycThree_mul_torusHom] at h
  · rintro ⟨⟨a, b⟩, hab, hg⟩
    obtain ⟨ha, hb⟩ := Subgroup.mem_prod.mp hab
    change torusHom (a, b) = cycThree * g * cycThree⁻¹ at hg
    have hg' : g = cycThree⁻¹ * torusHom (a, b) * cycThree := by rw [hg]; group
    have h := mem_torusPow hb (inv_mem (mul_mem ha hb))
    rwa [← inv_mul_cancel_left cycThree (torusHom (b, (a * b)⁻¹)), ← torusHom_mul_cycThree,
      ← mul_assoc, ← hg'] at h

theorem isPGroup_zpowers_cycThree :
    IsPGroup 3 (Subgroup.zpowers (cycThree : GL (Fin 3) K)) := by
  rintro ⟨g, hg⟩
  refine ⟨1, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_one]
  exact pow_eq_one_of_mem_zpowers cycThree_pow_three hg

theorem isPGroup_cycTorus {μ : Kˣ} {k : ℕ} (hμ : μ ^ 3 ^ k = 1) :
    IsPGroup 3 (Subgroup.zpowers (cycThree : GL (Fin 3) K) ⊔ torusPow μ : Subgroup _) :=
  IsPGroup.to_sup_of_normal_right' isPGroup_zpowers_cycThree (isPGroup_torusPow hμ)
    (Subgroup.zpowers_le.mpr (cycThree_mem_normalizer_torusPow μ))

theorem torusHom_inv_mem_cycTorus (μ : Kˣ) :
    torusHom (μ, μ⁻¹) ∈ (Subgroup.zpowers (cycThree : GL (Fin 3) K) ⊔ torusPow μ : Subgroup _) :=
  Subgroup.mem_sup_right (mem_torusPow (Subgroup.mem_zpowers μ)
    (inv_mem (Subgroup.mem_zpowers μ)))

theorem cycThree_mem_cycTorus (μ : Kˣ) :
    cycThree ∈ (Subgroup.zpowers (cycThree : GL (Fin 3) K) ⊔ torusPow μ : Subgroup _) :=
  Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

theorem cycTorus_le_slPi {π : Bool} {p f : ℕ} (hK : PiField π p f K) {μ : Kˣ}
    (hμ : μ ∈ rootsOfUnity (qSubPi π (p ^ f)) K) :
    (Subgroup.zpowers (cycThree : GL (Fin 3) K) ⊔ torusPow μ : Subgroup _) ≤
      slPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  refine sup_le (Subgroup.zpowers_le.mpr (cycThree_mem_slPi hπ)) ?_
  rintro _ ⟨⟨a, b⟩, hab, rfl⟩
  obtain ⟨ha, hb⟩ := Subgroup.mem_prod.mp hab
  have hle : Subgroup.zpowers μ ≤ rootsOfUnity (qSubPi π (p ^ f)) K :=
    Subgroup.zpowers_le.mpr hμ
  exact torusHom_mem_slPi hK (hle ha) (hle hb)

theorem exists_conj_mem_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) {P : Subgroup G} (hP : IsPGroup p P) :
    ∃ x : G, ∀ g ∈ P, x * g * x⁻¹ ∈ (T : Subgroup G) := by
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G S T
  refine ⟨x, fun g hg => ?_⟩
  rw [← hx, Sylow.coe_subgroup_smul]
  have := Subgroup.smul_mem_pointwise_smul g (MulAut.conj x) (S : Subgroup G) (hS hg)
  rwa [MulAut.smul_def, MulAut.conj_apply] at this

theorem exists_orderOf_eq_of_dvd_card {G : Type*} [Group G] [IsCyclic G] [Finite G] {d : ℕ}
    (hd : d ∣ Nat.card G) : ∃ g : G, orderOf g = d := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := G)
  have hord := orderOf_eq_card_of_forall_mem_zpowers hγ
  obtain ⟨m, hm⟩ := hd
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    omega
  refine ⟨γ ^ m, ?_⟩
  rw [orderOf_pow_of_dvd hm0 (by rw [hord, hm]; exact Dvd.intro_left d rfl), hord, hm,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]

end PGroups

end CFSG.RankThree.PartTwo.KFacts

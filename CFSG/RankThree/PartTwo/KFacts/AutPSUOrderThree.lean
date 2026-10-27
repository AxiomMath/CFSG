module

public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful
import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
import CFSG.RankThree.SteinbergR3ELinearTwoFieldDescent
import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut map_bar_comm)
open Matrix

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

section Descent

theorem map_bar_mul3 (X Y : Matrix (Fin 3) (Fin 3) K) :
    (X * Y).map h.bar = X.map h.bar * Y.map h.bar :=
  Matrix.map_mul (f := h.bar)

theorem map_bar_smul3 (c : K) (X : Matrix (Fin 3) (Fin 3) K) :
    (c • X).map h.bar = h.bar c • X.map h.bar := by
  ext i j
  simp

theorem bar_transpose_bar3 (X : Matrix (Fin 3) (Fin 3) K) :
    (((X.map h.bar)ᵀ).map h.bar)ᵀ = X := by
  ext i j
  simp [UnitaryFieldData.bar_bar]

theorem map_map_bar_comm3 (σ : K ≃+* K) (X : Matrix (Fin 3) (Fin 3) K) :
    (X.map h.bar).map σ = (X.map σ).map h.bar := by
  ext i j
  simp [map_bar_comm h σ]

theorem transpose_map_bar_map3 (σ : K ≃+* K) (X : Matrix (Fin 3) (Fin 3) K) :
    ((X.map h.bar)ᵀ).map σ = ((X.map σ).map h.bar)ᵀ := by
  ext i j
  simp [map_bar_comm h σ]

theorem eq_one_of_smul_eq_self {a : K} {X : Matrix (Fin 3) (Fin 3) K} (hX : X ≠ 0)
    (h1 : a • X = X) : a = 1 :=
  smul_left_injective K hX (h1.trans (one_smul K X).symm)

variable {h}

theorem exists_unitary_mul_map_eq_scalar_mul {σ : K ≃+* K} (hσ : orderOf σ = 3)
    (A : unitaryIsom3 h) {c : Kˣ}
    (hc : GeneralLinearGroup.scalar (Fin 3) c = (A : GL (Fin 3) K) *
      GeneralLinearGroup.map (σ : K →+* K) (A : GL (Fin 3) K) *
      GeneralLinearGroup.map ((σ * σ : K ≃+* K) : K →+* K) (A : GL (Fin 3) K)) :
    ∃ (H : unitaryIsom3 h) (d : Kˣ), (A : GL (Fin 3) K) * glAut σ (H : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) d * H := by
  classical
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ, pow_orderOf_eq_one]
  have hσσσ : ∀ x, σ (σ (σ x)) = x := fun x => iterate_three_apply_of_pow hσ3 x
  obtain ⟨H₁, d₁, hH₁⟩ :=
    exists_mul_map_eq_scalar_mul_of_orderOf_eq_three (n := 3) (by norm_num) hσ
      (A : GL (Fin 3) K) hc
  set M : Matrix (Fin 3) (Fin 3) K := ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  set X : Matrix (Fin 3) (Fin 3) K := (H₁ : Matrix (Fin 3) (Fin 3) K) with hX
  have hMu : (M.map h.bar)ᵀ * M = 1 := A.2
  have hMu' : M * (M.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hMu
  have hXσ : M * X.map σ = (d₁ : K) • X := by
    have h1 := congrArg (fun Y : GL (Fin 3) K => (Y : Matrix (Fin 3) (Fin 3) K)) hH₁
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
    rw [smul_eq_diagonal_mul]
    exact h1
  have hXσ' : X.map σ = (d₁ : K) • ((M.map h.bar)ᵀ * X) := by
    calc X.map σ = (M.map h.bar)ᵀ * (M * X.map σ) := by
          rw [← Matrix.mul_assoc, hMu, Matrix.one_mul]
      _ = _ := by rw [hXσ, Matrix.mul_smul]
  set B : Matrix (Fin 3) (Fin 3) K := (X.map h.bar)ᵀ * X with hB
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ = h.bar (d₁ : K) * d₁ := ⟨_, rfl⟩
  have hBσ : B.map σ = μ • B := by
    rw [hμ]
    rw [hB, map_mul_ringAut, transpose_map_bar_map3, hXσ', map_bar_smul3,
      Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_bar_mul3,
      Matrix.transpose_mul, bar_transpose_bar3, Matrix.mul_assoc, ← Matrix.mul_assoc M, hMu',
      Matrix.one_mul]
  have hXdet : X.det ≠ 0 := (Matrix.isUnits_det_units H₁).ne_zero
  have hBdet : B.det ≠ 0 := by
    rw [hB, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero ((map_ne_zero h.bar).mpr hXdet) hXdet
  have hB0 : B ≠ 0 := by
    intro h0
    rw [h0, Matrix.det_zero] at hBdet
    exact hBdet rfl
  have hμ3 : μ * σ μ * σ (σ μ) = 1 := by
    have h1 : ((B.map σ).map σ).map σ = B := by
      ext i j
      simp [hσσσ]
    rw [hBσ, map_smul_ringAut, hBσ, smul_smul, map_smul_ringAut, hBσ, smul_smul] at h1
    have h2 := eq_one_of_smul_eq_self hB0 h1
    rw [← h2, map_mul]
    ring
  have hd₁0 : (d₁ : K) ≠ 0 := d₁.ne_zero
  have hμ0 : μ ≠ 0 := by
    rw [hμ]
    exact mul_ne_zero ((map_ne_zero h.bar).mpr hd₁0) hd₁0
  let a : K ≃+ K :=
    { toFun := fun x => μ * σ x
      invFun := fun x => σ.symm (μ⁻¹ * x)
      left_inv := fun x => by
        simp only
        rw [inv_mul_cancel_left₀ hμ0, RingEquiv.symm_apply_apply]
      right_inv := fun x => by
        simp only
        rw [RingEquiv.apply_symm_apply, mul_inv_cancel_left₀ hμ0]
      map_add' := fun x y => by simp only [map_add, mul_add] }
  have ha : ∀ (c v : K), a (c • v) = σ c • a v := fun c v => by
    change μ * σ (c * v) = σ c * (μ * σ v)
    rw [map_mul]
    ring
  have hah : ∀ v, (⇑a)^[3] v = v := fun v => by
    change μ * σ (μ * σ (μ * σ v)) = v
    rw [map_mul, map_mul, map_mul, hσσσ]
    calc μ * (σ μ * (σ (σ μ) * v)) = (μ * σ μ * σ (σ μ)) * v := by ring
      _ = v := by rw [hμ3, one_mul]
  have hcard : Nat.card K = p ^ (2 * f) := h.card
  obtain ⟨h3, k₀, hk₀, hk₀card, b, hb, -⟩ :=
    CFSG.RankThree.Classical.semilinear_fixed_basis h.prime (by have := h.one_le; omega) hcard σ
      hσ (Module.finrank_self K) a ha hah
  have hw0 : b 0 ≠ 0 := b.ne_zero 0
  have hw : μ * σ (b 0) = b 0 := hb 0
  have hbarμ : h.bar μ = μ := by rw [hμ, map_mul, UnitaryFieldData.bar_bar, mul_comm]
  have hS : ∀ x, μ * σ x = x → μ * σ (h.bar x) = h.bar x := fun x hx => by
    rw [map_bar_comm h σ, ← hbarμ, ← map_mul, hx]
  have he : ∃ e, σ e = e ∧ h.bar e ≠ e := by
    by_contra hall
    push Not at hall
    have hτ : ∀ x, CFSG.LieType.BorelTits.unitaryInvolution K p f x = h.bar x := fun x => by
      rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, UnitaryFieldData.bar_apply]
    have hmem := CFSG.RankThree.LinearTwo.mem_zpowers_of_forall_fixed h.prime
      (by have := h.one_le; omega : 1 ≤ 2 * f) hcard σ
      (CFSG.LieType.BorelTits.unitaryInvolution K p f) fun x hx => by rw [hτ]; exact hall x hx
    have hdvd := orderOf_dvd_of_mem_zpowers hmem
    have hτ2 : orderOf (CFSG.LieType.BorelTits.unitaryInvolution K p f) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime ?_ ?_
      · ext x
        rw [pow_two, RingAut.mul_apply, hτ, hτ, UnitaryFieldData.bar_bar]
        rfl
      · intro h1
        obtain ⟨c, hc⟩ := h.exists_bar_ne
        apply hc
        rw [← hτ, h1]
        rfl
    rw [hτ2, hσ] at hdvd
    omega
  obtain ⟨e, hσe, hbare⟩ := he
  obtain ⟨t, ht0, hbart, hμt⟩ : ∃ t : K, t ≠ 0 ∧ h.bar t = t ∧ μ * σ t = t := by
    by_cases hwb : b 0 + h.bar (b 0) = 0
    · have hew : μ * σ (e * b 0) = e * b 0 := by
        rw [map_mul, hσe, mul_left_comm, hw]
      refine ⟨e * b 0 + h.bar (e * b 0), ?_, ?_, ?_⟩
      · have h1 : e * b 0 + h.bar (e * b 0) = (e - h.bar e) * b 0 := by
          rw [map_mul, show h.bar (b 0) = -b 0 by linear_combination hwb]
          ring
        rw [h1]
        exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hbare)) hw0
      · rw [map_add, UnitaryFieldData.bar_bar, add_comm]
      · rw [map_add, mul_add, hew, hS _ hew]
    · refine ⟨b 0 + h.bar (b 0), hwb, ?_, ?_⟩
      · rw [map_add, UnitaryFieldData.bar_bar, add_comm]
      · rw [map_add, mul_add, hw, hS _ hw]
  have hBherm : (B.map h.bar)ᵀ = B := by
    rw [hB, map_bar_mul3, Matrix.transpose_mul, bar_transpose_bar3]
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix (Fin 3) (Fin 3) K, B' = t • B := ⟨_, rfl⟩
  have hB'σ : B'.map σ = B' := by
    rw [hB', map_smul_ringAut, hBσ, smul_smul, show σ t * μ = t by rw [mul_comm]; exact hμt]
  have hB'herm : (B'.map h.bar)ᵀ = B' := by
    rw [hB', map_bar_smul3, hbart, Matrix.transpose_smul, hBherm]
  have hB'det : B'.det ≠ 0 := by
    rw [hB', Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ ht0) hBdet
  have hk₀mem : ∀ x, x ∈ k₀ ↔ σ x = x := fun x => by
    rw [← SetLike.mem_coe, hk₀]
    rfl
  obtain ⟨g, hg⟩ : 3 ∣ f := Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3
  have hk₀card' : Nat.card k₀ = (p ^ g) ^ 2 := by
    rw [hk₀card, ← pow_mul]
    congr 1
    omega
  have : CharP k₀ p := ⟨fun m => by
    rw [← k₀.subtype_injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff K p m⟩
  have hbarpow : ∀ x : k₀, h.bar (x : K) = (x : K) ^ p ^ g := fun x => by
    have : Fintype k₀ := Fintype.ofFinite k₀
    have hx : x ^ Fintype.card k₀ = x := FiniteField.pow_card x
    rw [← Nat.card_eq_fintype_card, hk₀card'] at hx
    have hx' : (x : K) ^ (p ^ g) ^ 2 = x := by
      have h1 := congrArg Subtype.val hx
      rwa [SubmonoidClass.coe_pow] at h1
    rw [UnitaryFieldData.bar_apply, hg, show p ^ (3 * g) = (p ^ g) ^ 2 * p ^ g by ring, pow_mul,
      hx']
  have hB'mem : ∀ i j, B' i j ∈ k₀ := fun i j =>
    (hk₀mem _).mpr (congrFun (congrFun hB'σ i) j)
  let B₀ : Matrix (Fin 3) (Fin 3) k₀ := fun i j => ⟨B' i j, hB'mem i j⟩
  have hτ₀ : ∀ x : k₀, (CFSG.LieType.BorelTits.unitaryInvolution k₀ p g x : K) =
      h.bar (x : K) := fun x => by
    rw [hbarpow, CFSG.LieType.BorelTits.unitaryInvolution_apply, SubmonoidClass.coe_pow]
  have hB₀herm : CFSG.LieType.Universal.Unitary.conjTr
      (CFSG.LieType.BorelTits.unitaryInvolution k₀ p g) B₀ = B₀ := by
    ext i j
    change (CFSG.LieType.BorelTits.unitaryInvolution k₀ p g (B₀ j i) : K) = B' i j
    rw [hτ₀]
    exact congrFun (congrFun hB'herm i) j
  have hB₀map : B₀.map k₀.subtype = B' := by
    ext i j
    rfl
  have hB₀det : B₀.det ≠ 0 := by
    intro h0
    apply hB'det
    rw [← hB₀map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  obtain ⟨P₀, hP₀⟩ := CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one (F := k₀) (p := p)
    (f := g) hk₀card' hB₀herm hB₀det
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin 3) (Fin 3) K,
      P = (P₀ : Matrix (Fin 3) (Fin 3) k₀).map k₀.subtype := ⟨_, rfl⟩
  have hPσ : P.map σ = P := by
    rw [hP]
    ext i j
    exact (hk₀mem _).mp ((P₀ : Matrix (Fin 3) (Fin 3) k₀) i j).2
  have hPu : (P.map h.bar)ᵀ * B' * P = 1 := by
    have h1 := congrArg k₀.subtype.mapMatrix hP₀
    rw [map_mul, map_mul, map_one] at h1
    have hc : k₀.subtype.mapMatrix (CFSG.LieType.Universal.Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution k₀ p g) (P₀ : Matrix (Fin 3) (Fin 3) k₀)) =
          (P.map h.bar)ᵀ := by
      rw [hP]
      ext i j
      exact hτ₀ _
    rw [hc, RingHom.mapMatrix_apply, hB₀map, RingHom.mapMatrix_apply, ← hP] at h1
    exact h1
  obtain ⟨s, hs⟩ := (unitary_field_norm h).1 ⟨t, (UnitaryFieldData.mem_fixedField h).mpr hbart⟩
  have hs' : s * h.bar s = t := by
    have h1 := congrArg Subtype.val hs
    rwa [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm] at h1
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hs'
    exact ht0 hs'.symm
  set Hgl : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) (Units.mk0 s hs0) * H₁ *
    Matrix.GeneralLinearGroup.map k₀.subtype P₀ with hHgl
  have hHmat : (Hgl : Matrix (Fin 3) (Fin 3) K) = s • (X * P) := by
    rw [hHgl, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0,
      Matrix.scalar_apply, ← smul_eq_diagonal_mul, Matrix.smul_mul, hP]
    rfl
  have hHu : Hgl ∈ unitaryIsom3 h := by
    rw [mem_unitaryIsom3, hHmat, map_bar_smul3, map_bar_mul3, Matrix.transpose_smul,
      Matrix.transpose_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hPu, hB', hB]
    rw [show h.bar s * s = t by rw [mul_comm]; exact hs']
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hd0 : σ s * (d₁ : K) * s⁻¹ ≠ 0 :=
    mul_ne_zero (mul_ne_zero ((map_ne_zero σ).mpr hs0) hd₁0) (inv_ne_zero hs0)
  have key : M * (Hgl : Matrix (Fin 3) (Fin 3) K).map σ =
      (σ s * (d₁ : K) * s⁻¹) • (Hgl : Matrix (Fin 3) (Fin 3) K) := by
    rw [hHmat, map_smul_ringAut, map_mul_ringAut, hPσ, Matrix.mul_smul, ← Matrix.mul_assoc, hXσ,
      Matrix.smul_mul, smul_smul, smul_smul]
    congr 1
    field_simp
  refine ⟨⟨Hgl, hHu⟩, Units.mk0 _ hd0, ?_⟩
  apply Units.ext
  change M * ((Hgl : Matrix (Fin 3) (Fin 3) K).map σ) =
    Matrix.scalar (Fin 3) (σ s * (d₁ : K) * s⁻¹) * (Hgl : Matrix (Fin 3) (Fin 3) K)
  rw [Matrix.scalar_apply, ← smul_eq_diagonal_mul]
  exact key

end Descent

variable {h}

theorem psuConj_mul_psuField_mul (A B : unitaryIsom3 h) (σ τ : K ≃+* K) :
    psuConj h A * psuField h σ * (psuConj h B * psuField h τ) =
      psuConj h (A * ⟨glAut σ B, glAut_mem_unitaryIsom3 σ B.2⟩) * psuField h (σ * τ) := by
  calc psuConj h A * psuField h σ * (psuConj h B * psuField h τ) =
      psuConj h A * (psuField h σ * psuConj h B * (psuField h σ)⁻¹) *
        (psuField h σ * psuField h τ) := by group
    _ = _ := by rw [psuField_mul_psuConj_mul_inv, ← map_mul, ← map_mul]

theorem psuConj_scalar {c : Kˣ} (hc : GeneralLinearGroup.scalar (Fin 3) c ∈ unitaryIsom3 h) :
    psuConj h ⟨_, hc⟩ = 1 :=
  psuConj_eq_one_of_coe_eq_scalar rfl

theorem unitary_order_three_field_descent (hq : 2 < p ^ f) (α : MulAut (unitaryPSU h 3))
    (hα : α ^ 3 = 1) (hD : α ∉ (psuConj h).range) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧ ∃ H : unitaryIsom3 h,
      α = psuConj h H * psuField h σ * (psuConj h H)⁻¹ := by
  obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at hD
    exact hD ⟨A, rfl⟩
  have h3 : psuConj h (A * ⟨glAut σ A, glAut_mem_unitaryIsom3 σ A.2⟩ *
      ⟨glAut (σ * σ) A, glAut_mem_unitaryIsom3 (σ * σ) A.2⟩) * psuField h (σ * σ * σ) = 1 := by
    rw [← hα, pow_three', psuConj_mul_psuField_mul, psuConj_mul_psuField_mul]
  obtain ⟨hσσσ, c, -, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ h3
  have hσ3 : orderOf σ = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (by rw [pow_three', hσσσ]) hσ1
  have hc' : GeneralLinearGroup.scalar (Fin 3) c = (A : GL (Fin 3) K) *
      GeneralLinearGroup.map (σ : K →+* K) (A : GL (Fin 3) K) *
      GeneralLinearGroup.map ((σ * σ : K ≃+* K) : K →+* K) (A : GL (Fin 3) K) := by
    rw [← hc]
    rfl
  obtain ⟨H, d, hH⟩ := exists_unitary_mul_map_eq_scalar_mul hσ3 A hc'
  refine ⟨σ, hσ3, H, ?_⟩
  have hdmem : GeneralLinearGroup.scalar (Fin 3) d ∈ unitaryIsom3 h := by
    have h1 : GeneralLinearGroup.scalar (Fin 3) d =
        (A : GL (Fin 3) K) * glAut σ (H : GL (Fin 3) K) * (H : GL (Fin 3) K)⁻¹ := by
      rw [hH, mul_inv_cancel_right]
    rw [h1]
    exact mul_mem (mul_mem A.2 (glAut_mem_unitaryIsom3 σ H.2)) (inv_mem H.2)
  have hAeq : A = ⟨_, hdmem⟩ * H * ⟨glAut σ H, glAut_mem_unitaryIsom3 σ H.2⟩⁻¹ :=
    Subtype.ext (eq_mul_inv_of_mul_eq hH)
  rw [hAeq, map_mul, map_mul, map_inv, psuConj_scalar, one_mul,
    ← psuField_mul_psuConj_mul_inv σ H]
  group

theorem isField_psu3_of_pow_three_eq_one (hq : 2 < p ^ f) {α : MulAut (unitaryPSU h 3)}
    (hα : α ^ 3 = 1) (hD : α ∉ (psuConj h).range) : (stdPinnedPSU3 h).IsField α := by
  obtain ⟨σ, hσ, H, rfl⟩ := unitary_order_three_field_descent hq α hα hD
  refine ⟨psuField h σ, ⟨σ, rfl⟩, fun h1 => ?_, psuConj h H, ⟨H, rfl⟩, rfl⟩
  have h2 := (eq_one_of_psuConj_mul_psuField_eq_one 1 σ (by rw [map_one, one_mul, h1])).1
  rw [h2, orderOf_one] at hσ
  omega

theorem hasKind_psu3_diagonal_or_field_of_pow_three_eq_one (hq : 2 < p ^ f)
    {α : MulAut (unitaryPSU h 3)} (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    (stdPinnedPSU3 h).HasKind α .diagonal ∨ (stdPinnedPSU3 h).HasKind α .field := by
  by_cases hD : α ∈ (psuConj h).range
  · exact Or.inl ⟨hD, hout⟩
  · exact Or.inr (isField_psu3_of_pow_three_eq_one hq hα hD)

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

theorem inducesKindPSU3_diagonal_or_field (hq : 2 < p ^ f) {x : G} (hx3 : x ^ 3 = 1)
    (hout : InducesOuterTheta x L) (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitaryPSU h 3) :
    InducesKind L (stdPinnedPSU3 h) e x .diagonal ∨
      InducesKind L (stdPinnedPSU3 h) e x .field := by
  obtain ⟨hx, -⟩ := id hout
  rcases hasKind_psu3_diagonal_or_field_of_pow_three_eq_one hq
    (inducedAutHom_pow_eq_one L e hx hx3) ((not_isInnerAut_inducedAutHom_iff L e hx).mpr hout)
    with h | h
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr ⟨hx, h⟩

theorem inducesKindSU3_inner_or_diagonal_or_field (hq : 2 < p ^ f) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU p f K 3) :
    (stdPinnedPSU3 h).HasKind (MulAut.congr (suCenterEquiv h hq)
        (centerDescend _ (inducedAutHom L e ⟨x, hx⟩))) .inner ∨
      (stdPinnedPSU3 h).HasKind (MulAut.congr (suCenterEquiv h hq)
        (centerDescend _ (inducedAutHom L e ⟨x, hx⟩))) .diagonal ∨
      (stdPinnedPSU3 h).HasKind (MulAut.congr (suCenterEquiv h hq)
        (centerDescend _ (inducedAutHom L e ⟨x, hx⟩))) .field := by
  by_cases hin : IsInnerAut (MulAut.congr (suCenterEquiv h hq)
      (centerDescend _ (inducedAutHom L e ⟨x, hx⟩)))
  · exact Or.inl hin
  · refine Or.inr (hasKind_psu3_diagonal_or_field_of_pow_three_eq_one hq ?_ hin)
    rw [← map_pow, ← map_pow, inducedAutHom_pow_eq_one L e hx hx3, map_one, map_one]

end Induced

end CFSG.RankThree.PartTwo.KFacts

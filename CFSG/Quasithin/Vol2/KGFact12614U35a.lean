module

public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar

public section

namespace CFSG.Quasithin.H13.U35A6

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts

variable {K : Type} [Field K]

@[expose] def dMat (ω : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2]

@[expose] def cMat : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem dMat_mul (ω : K) (hω : ω ^ 3 = 1) : dMat ω * dMat (ω ^ 2) = 1 := by
  have h4 : ω ^ 4 = ω := by rw [pow_succ, hω, one_mul]
  have h6 : ω ^ 2 * (ω ^ 2) ^ 2 = 1 := by
    rw [show ω ^ 2 * (ω ^ 2) ^ 2 = (ω ^ 3) ^ 2 by ring, hω, one_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dMat, Matrix.mul_apply, Fin.sum_univ_three, ← pow_succ', hω, h6]

theorem dMat_mul' (ω : K) (hω : ω ^ 3 = 1) : dMat (ω ^ 2) * dMat ω = 1 := by
  have h6 : (ω ^ 2) ^ 2 * ω ^ 2 = 1 := by
    rw [show (ω ^ 2) ^ 2 * ω ^ 2 = (ω ^ 3) ^ 2 by ring, hω, one_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dMat, Matrix.mul_apply, Fin.sum_univ_three, ← pow_succ, hω, h6]

theorem cMat_mul : (cMat : Matrix (Fin 3) (Fin 3) K) * cMatᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem cMat_mul' : (cMat : Matrix (Fin 3) (Fin 3) K)ᵀ * cMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem dMat_cMat (ω : K) (hω : ω ^ 3 = 1) :
    dMat ω * cMat = ω • (cMat * dMat ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dMat, cMat, Matrix.mul_apply, Fin.sum_univ_three, ← pow_succ', hω]
  ring

@[expose] def dU (ω : K) (hω : ω ^ 3 = 1) : GL (Fin 3) K :=
  ⟨dMat ω, dMat (ω ^ 2), dMat_mul ω hω, dMat_mul' ω hω⟩

@[expose] def cU : GL (Fin 3) K := ⟨cMat, cMatᵀ, cMat_mul, cMat_mul'⟩

theorem bar_omega (h : UnitaryFieldData 5 1 K) {ω : K} (hω : ω ^ 3 = 1) : h.bar ω = ω ^ 2 := by
  rw [h.bar_apply, pow_one, show ω ^ 5 = ω ^ 3 * ω ^ 2 by ring, hω, one_mul]

theorem dU_mem (h : UnitaryFieldData 5 1 K) {ω : K} (hω : ω ^ 3 = 1) :
    dU ω hω ∈ unitarySU 5 1 K 3 := by
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · show (dMat ω).det = 1
    rw [Matrix.det_fin_three]
    simp [dMat, ← pow_succ', hω]
  · show ((dMat ω).map h.bar)ᵀ * dMat ω = 1
    have h1 : ((dMat ω).map h.bar)ᵀ = dMat (ω ^ 2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [dMat, bar_omega h hω, map_pow]
    rw [h1]
    exact dMat_mul' ω hω

theorem cU_mem (h : UnitaryFieldData 5 1 K) : (cU : GL (Fin 3) K) ∈ unitarySU 5 1 K 3 := by
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · show (cMat : Matrix (Fin 3) (Fin 3) K).det = 1
    rw [Matrix.det_fin_three]
    simp [cMat]
  · show ((cMat : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * cMat = 1
    have h1 : (cMat : Matrix (Fin 3) (Fin 3) K).map h.bar = cMat := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [cMat]
    rw [h1]
    exact cMat_mul'

section Fix

variable (h : UnitaryFieldData 5 1 K)

@[expose] def g₁ {ω : K} (hω : ω ^ 3 = 1) : unitarySU 5 1 K 3 := ⟨dU ω hω, dU_mem h hω⟩

@[expose] def g₂ : unitarySU 5 1 K 3 := ⟨cU, cU_mem h⟩

theorem exists_smul_of_fix (B : unitaryIsom3 h) (σ : K ≃+* K) (g : unitarySU 5 1 K 3)
    (hfix : (psuConj h B * psuField h σ) (g : unitaryPSU h 3) = g) :
    ∃ c : K, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      c • (((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ *
        (((B : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  rw [MulAut.mul_apply, psuField_mk, psuConj_mk] at hfix
  have h1 := (QuotientGroup.eq).1 hfix
  obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.1 h1
  refine ⟨(c : K), ?_⟩
  set x := suConj h B (suField h σ g) with hx
  have h2 : ((g : GL (Fin 3) K)) =
      (x : GL (Fin 3) K) * Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    rw [← hc]
    simp
  have h3 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) h2
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hx, coe_suConj, coe_suField,
    UnitaryHigher.coe_glAut] at h3
  refine h3.trans ?_
  rw [Subgroup.coe_inv, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
    Matrix.mul_one]

@[expose] def psiM (Bm Bi : Matrix (Fin 3) (Fin 3) K) (σ : K ≃+* K) (X : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K :=
  Bm * X.map σ * Bi

theorem psiM_mul {Bm Bi : Matrix (Fin 3) (Fin 3) K} (hBB : Bi * Bm = 1) (σ : K ≃+* K)
    (X Y : Matrix (Fin 3) (Fin 3) K) : psiM Bm Bi σ (X * Y) = psiM Bm Bi σ X * psiM Bm Bi σ Y := by
  simp only [psiM, Matrix.map_mul]
  calc Bm * (X.map σ * Y.map σ) * Bi = Bm * X.map σ * (Bi * Bm) * Y.map σ * Bi := by
        rw [hBB, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = Bm * X.map σ * Bi * (Bm * Y.map σ * Bi) := by simp only [Matrix.mul_assoc]

theorem psiM_smul (Bm Bi : Matrix (Fin 3) (Fin 3) K) (σ : K ≃+* K) (a : K)
    (X : Matrix (Fin 3) (Fin 3) K) : psiM Bm Bi σ (a • X) = σ a • psiM Bm Bi σ X := by
  have : (a • X).map σ = σ a • X.map σ := by
    ext i j
    simp [Matrix.map_apply, map_mul]
  simp only [psiM, this, Matrix.mul_smul, Matrix.smul_mul]

theorem sigma_eq_of_fix {ω : K} (hω : ω ^ 3 = 1) (B : unitaryIsom3 h) (σ : K ≃+* K)
    (h1 : (psuConj h B * psuField h σ) (g₁ h hω : unitaryPSU h 3) = g₁ h hω)
    (h2 : (psuConj h B * psuField h σ) (g₂ h : unitaryPSU h 3) = g₂ h) : σ ω = ω := by
  obtain ⟨c₁, hc₁⟩ := exists_smul_of_fix h B σ _ h1
  obtain ⟨c₂, hc₂⟩ := exists_smul_of_fix h B σ _ h2
  have hBB : (((B : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set ψ := psiM ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    (((B : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ with hψ
  have hc₁' : dMat ω = c₁ • ψ (dMat ω) := hc₁
  have hc₂' : (cMat : Matrix (Fin 3) (Fin 3) K) = c₂ • ψ cMat := hc₂
  have hrel := dMat_cMat ω hω
  have h3 : ψ (dMat ω) * ψ cMat = σ ω • (ψ cMat * ψ (dMat ω)) := by
    rw [hψ, ← psiM_mul hBB, hrel, psiM_smul, psiM_mul hBB]
  have key : dMat ω * cMat = σ ω • (cMat * dMat ω) := by
    calc dMat ω * cMat = (c₁ • ψ (dMat ω)) * (c₂ • ψ cMat) := by rw [← hc₁', ← hc₂']
      _ = (c₁ * c₂) • (ψ (dMat ω) * ψ cMat) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = (c₁ * c₂) • (σ ω • (ψ cMat * ψ (dMat ω))) := by rw [h3]
      _ = σ ω • ((c₂ • ψ cMat) * (c₁ • ψ (dMat ω))) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul, smul_smul]
        congr 1
        ring
      _ = σ ω • (cMat * dMat ω) := by rw [← hc₁', ← hc₂']
  have h4 := congrFun (congrFun (hrel.symm.trans key) 1) 0
  simp [cMat, dMat] at h4
  exact h4.symm

end Fix

theorem eq_one_of_fix_omega (h : UnitaryFieldData 5 1 K) {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {σ : K ≃+* K} (hσ : σ ω = ω) : σ = 1 := by
  have := h.finite
  have hK : Nat.card K = 5 ^ 2 := h.card
  have h2 : Nat.card (K ≃+* K) = 2 := (card_ringAut_and_isCyclic Nat.prime_five K hK).1
  have hinj : Function.Injective h.bar := h.bar.injective
  let β : K ≃+* K := RingEquiv.ofBijective h.bar ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  have hβω : β ω = ω ^ 2 := bar_omega h hω
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  have hsq : ω ^ 2 ≠ ω := by
    intro h1
    apply hω1
    have h3 : ω * ω = ω * 1 := by rw [mul_one, ← sq, h1]
    exact mul_left_cancel₀ hω0 h3
  have hβ1 : β ≠ 1 := by
    intro h1
    apply hsq
    rw [← hβω, h1]
    rfl
  by_contra hne
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : K ≃+* K)).1 h2
  have : σ = β := (hy σ hne).trans (hy β hβ1).symm
  rw [this, hβω] at hσ
  exact hsq hσ

theorem psuConj_scalar (h : UnitaryFieldData 5 1 K) (s : unitaryIsom3 h) (c : Kˣ)
    (hs : (s : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c) : psuConj h s = 1 :=
  CFSG.RankThree.PartTwo.KFacts.psuConj_eq_one_of_coe_eq_scalar hs

theorem gcd_six_two_pow (n : ℕ) : Nat.gcd 6 (2 ^ (n + 1)) = 2 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_succ, mul_comm (2 ^ n) 2, Nat.gcd_mul_left,
    (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)).gcd_eq_one, mul_one]

theorem exists_conj_of_pow (h : UnitaryFieldData 5 1 K) (B : unitaryIsom3 h) {n : ℕ}
    (hB : psuConj h B ^ 2 ^ n = 1) :
    ∃ g : unitarySU 5 1 K 3, psuConj h B = MulAut.conj (g : unitaryPSU h 3) := by
  have h1 : psuConj h (B ^ 2 ^ n) * psuField h 1 = 1 := by rw [map_pow, hB, map_one, mul_one]
  obtain ⟨-, c, hcn, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ h1
  set d := ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det with hd
  have hu : (((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := mem_unitaryIsom3.1 B.2
  have hd6 : d ^ 6 = 1 := by
    have := congrArg Matrix.det hu
    have hdet : (((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar).det = h.bar d := by
      rw [hd, RingHom.map_det]
      rfl
    rw [Matrix.det_mul, Matrix.det_transpose, hdet, Matrix.det_one, h.bar_apply, ← hd] at this
    calc d ^ 6 = d ^ 5 ^ 1 * d := by ring
      _ = 1 := this
  have hdn : d ^ 2 ^ n = (c : K) ^ 3 := by
    have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K).det) hc
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, Matrix.det_pow,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    rw [hd]
    exact this
  have hc6 : (c : K) ^ 6 = 1 := by
    have : h.norm (c : K) = (c : K) ^ 6 := by
      rw [UnitaryFieldData.norm, h.bar_apply]
      ring
    rw [← this]
    exact hcn
  have hd2 : d ^ 2 = 1 := by
    have h3 : d ^ 2 ^ (n + 1) = 1 := by
      rw [pow_succ, pow_mul, hdn, ← pow_mul]
      exact hc6
    have := pow_gcd_eq_one.2 ⟨hd6, h3⟩
    rwa [gcd_six_two_pow] at this
  have hd' : d = 1 ∨ d = -1 := mul_self_eq_one_iff.1 (by rw [← sq]; exact hd2)
  rcases hd' with hd1 | hd1
  · have hmem : (B : GL (Fin 3) K) ∈ unitarySU 5 1 K 3 := (mem_unitarySU_iff h).2 ⟨hd1, hu⟩
    refine ⟨⟨B, hmem⟩, ?_⟩
    rw [conj_mk_eq_psuConj]
  ·
    have hs : Matrix.GeneralLinearGroup.scalar (Fin 3) (-1 : Kˣ) ∈ unitaryIsom3 h := by
      rw [mem_unitaryIsom3]
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_map]
    set s : unitaryIsom3 h := ⟨_, hs⟩ with hsdef
    have hsB : ((s * B : unitaryIsom3 h) : GL (Fin 3) K) ∈ unitarySU 5 1 K 3 := by
      refine (mem_unitarySU_iff h).2 ⟨?_, mem_unitaryIsom3.1 (s * B).2⟩
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, hsdef,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← hd, hd1]
      norm_num
    refine ⟨⟨_, hsB⟩, ?_⟩
    rw [conj_mk_eq_psuConj]
    have e : (⟨((⟨_, hsB⟩ : unitarySU 5 1 K 3) : GL (Fin 3) K), _⟩ : unitaryIsom3 h) = s * B :=
      Subtype.ext rfl
    rw [e, map_mul, psuConj_scalar h s (-1) rfl, one_mul]

section Gens

variable (h : UnitaryFieldData 5 1 K)

theorem scalar_mul_comm (c : Kˣ) (A : GL (Fin 3) K) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c * A =
      A * Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_commute (c : K) (fun r' => Commute.all _ r') _).eq

theorem omega_ne_zero {ω : K} (hω : ω ^ 3 = 1) : ω ≠ 0 := by
  rintro rfl
  norm_num at hω

theorem dU_cU {ω : K} (hω : ω ^ 3 = 1) :
    dU ω hω * cU = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ω (omega_ne_zero hω)) *
      (cU * dU ω hω) := by
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  show dMat ω * cMat = Matrix.scalar (Fin 3) ω * (cMat * dMat ω)
  rw [dMat_cMat ω hω, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
    Matrix.one_mul]

theorem x_comm {ω : K} (hω : ω ^ 3 = 1) :
    (g₁ h hω : unitaryPSU h 3) * (g₂ h : unitaryPSU h 3) = (g₂ h : unitaryPSU h 3) * g₁ h hω := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_unitaryScalars]
  set u : Kˣ := Units.mk0 ω (omega_ne_zero hω) with hu
  have hu3 : u ^ 3 = 1 := Units.ext (by simp [hu, hω])
  refine ⟨u⁻¹, ?_, ?_, ?_⟩
  · rw [UnitaryFieldData.norm, h.bar_apply]
    have : ((u⁻¹ : Kˣ) : K) * ((u⁻¹ : Kˣ) : K) ^ 5 ^ 1 = ((u ^ 3) ^ 2)⁻¹.val := by
      push_cast
      ring
    rw [this, hu3]
    simp
  · rw [inv_pow, hu3, inv_one]
  · show (dU ω hω * cU)⁻¹ * (cU * dU ω hω) = _
    rw [dU_cU hω, _root_.mul_inv_rev, mul_assoc, ← hu, ← map_inv, scalar_mul_comm,
      inv_mul_cancel_left]

theorem x1_pow {ω : K} (hω : ω ^ 3 = 1) : (g₁ h hω : unitaryPSU h 3) ^ 3 = 1 := by
  rw [← QuotientGroup.mk_pow]
  have : g₁ h hω ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    show dMat ω ^ 3 = 1
    have e1 : ω * (ω * ω) = 1 := by rw [← hω]; ring
    have e2 : ω ^ 2 * (ω ^ 2 * ω ^ 2) = 1 := by
      rw [show ω ^ 2 * (ω ^ 2 * ω ^ 2) = (ω ^ 3) ^ 2 by ring, hω, one_pow]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dMat, pow_three, Matrix.mul_apply, Fin.sum_univ_three, e1, e2]
  rw [this, QuotientGroup.mk_one]

theorem x2_pow : (g₂ h : unitaryPSU h 3) ^ 3 = 1 := by
  rw [← QuotientGroup.mk_pow]
  have : g₂ h ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    show (cMat : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cMat, pow_three, Matrix.mul_apply, Fin.sum_univ_three]
  rw [this, QuotientGroup.mk_one]

end Gens

end CFSG.Quasithin.H13.U35A6

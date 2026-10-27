module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotHsylBasic
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleBasic
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalUnitaryLagrangian
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHsyl
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotTorus

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

@[expose] def toGram (g : unitarySU 2 f K n) :
    gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  ⟨g, by rw [CFSG.ComponentClassification.OutcomeLocal.gramSU_one_eq]; exact g.2⟩

theorem coe_toGram (g : unitarySU 2 f K n) :
    ((toGram h g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) =
      g :=
  rfl

theorem primeFormOneEquiv_toGram (g : unitarySU 2 f K n) :
    CFSG.ComponentClassification.OutcomeLocal.primeFormOneEquiv h n
        ((toGram h g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
          primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      unitaryProj h n g :=
  CFSG.ComponentClassification.OutcomeLocal.primeFormOneEquiv_mk h (toGram h g) g rfl

theorem congr_symm_apply_toGram_of_apply_eq {β : MulAut (unitaryPSU h n)}
    {g : unitarySU 2 f K n} (hg : β (unitaryProj h n g) = unitaryProj h n g) :
    MulAut.congr (CFSG.ComponentClassification.OutcomeLocal.primeFormOneEquiv h n).symm β
        ((toGram h g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
          primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      ((toGram h g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
        primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  rw [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.trans_apply,
    primeFormOneEquiv_toGram, hg,
    ← primeFormOneEquiv_toGram, MulEquiv.symm_apply_apply]

theorem eq_one_of_two_group_fix_of_five_le (hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {X : Subgroup (unitaryPSU h n)} (hX : X ≤ rootSU2 h a b) (hXo : Odd (Nat.card X))
    (hX1 : X ≠ ⊥) {β : MulAut (unitaryPSU h n)} (hβX : ∀ x ∈ X, β x = x)
    (hβD : ∀ d ∈ blockSU h ({a, b}ᶜ : Finset (Fin n)), β d = d) {k : ℕ}
    (hβk : β ^ 2 ^ k = 1) : β = 1 := by
  have := h.charP
  have := h.finite
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC1 (by omega) (by omega)
    (MulAut.congr (CFSG.ComponentClassification.OutcomeLocal.primeFormOneEquiv h n).symm β)
  have hfix : ∀ g : unitarySU 2 f K n, β (unitaryProj h n g) = unitaryProj h n g →
      primeFormPsi h hC1 ⟨A, φ⟩ ((toGram h g : gramSU h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
        ((toGram h g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
          primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := fun g hg => by
    rw [hAφ]
    exact congr_symm_apply_toGram_of_apply_eq h hg
  have hAu : (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    have h0 : (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
        (1 : Matrix (Fin n) (Fin n) K) * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
      mem_primeFormUnitary.1 A.2
    rwa [Matrix.mul_one] at h0
  have hJ3 : 3 ≤ ({a, b}ᶜ : Finset (Fin n)).card := by
    rw [card_compl_pair hab]
    omega
  obtain ⟨hφ1, μ, hμN, hAμ⟩ := eq_one_and_agrees_of_forall_involution h hJ3 hAu
    (fun g hgJ hgg => UnitaryLagrangian.mul_glAut_eq_of_psi_apply_eq h (by omega) hC1 A φ
      (toGram h g) (by rw [coe_toGram, ← Subgroup.coe_mul, hgg, OneMemClass.coe_one])
      (hfix g (hβD _ (unitaryProj_mem_blockSU h hgJ))))
  subst hφ1
  obtain ⟨x, hxX, y, hy, rfl, -, -, hyk⟩ := exists_lift_of_le_rootSU2 h hX hXo hX1
  set Y : Matrix (Fin n) (Fin n) K := ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hYdef
  set M : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMdef
  have hYa : ∀ i j, (i ∉ ({a, b} : Finset (Fin n)) ∨ j ∉ ({a, b} : Finset (Fin n))) →
      Y i j = (1 : Matrix (Fin n) (Fin n) K) i j := (mem_unitaryBlock h).1 hy
  have hAy : Y * M = M * Y := by
    have h1 := hfix y (hβX _ hxX)
    rw [UnitaryLagrangian.primeFormPsi_apply_proj] at h1
    obtain ⟨c, -, -, hc⟩ := (QuotientGroup.eq (s := normOneScalars h _ n)).mp h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_one, MulAut.one_apply, coe_toGram] at hc
    have h3 : (y : GL (Fin n) K) =
        A * y * (A : GL (Fin n) K)⁻¹ * GeneralLinearGroup.scalar (Fin n) c := by
      rw [← hc, mul_inv_cancel_left]
    have hsA : GeneralLinearGroup.scalar (Fin n) c * (A : GL (Fin n) K) =
        A * GeneralLinearGroup.scalar (Fin n) c := (commute_scalar c (A : GL (Fin n) K)).eq.symm
    have h2 : (y : GL (Fin n) K) * A = A * y * GeneralLinearGroup.scalar (Fin n) c := by
      have e : (y : GL (Fin n) K) * A =
          A * y * (A : GL (Fin n) K)⁻¹ * GeneralLinearGroup.scalar (Fin n) c * A :=
        congrArg (· * (A : GL (Fin n) K)) h3
      rw [e, mul_assoc _ (GeneralLinearGroup.scalar (Fin n) c), hsA]
      group
    have h4 : Y * M = (c : K) • (M * Y) := by
      have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h2
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at this
      rw [this, scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    have hdetM : M.det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp (A : GL (Fin n) K).isUnit).ne_zero
    have hc1 := eq_one_of_mul_eq_smul_mul (lt_two_mul_card_compl_pair hn hab) hYa hdetM h4
    rw [hc1, one_smul] at h4
    exact h4
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, UnitaryFieldData.norm, zero_mul] at hμN
    exact zero_ne_one hμN
  set N : Matrix (Fin n) (Fin n) K := μ⁻¹ • M with hNdef
  have hN : ∀ i j, (i ∉ ({a, b} : Finset (Fin n)) ∨ j ∉ ({a, b} : Finset (Fin n))) →
      N i j = (1 : Matrix (Fin n) (Fin n) K) i j := by
    intro i j hij
    rw [hNdef, Matrix.smul_apply, smul_eq_mul, hAμ i j (by simpa only [Finset.mem_compl] using hij),
      ← mul_assoc, inv_mul_cancel₀ hμ0, one_mul]
  have hNy : Y * N = N * Y := by
    rw [hNdef, Matrix.mul_smul, Matrix.smul_mul, hAy]
  have hpow : primeFormPsi h hC1 ⟨A ^ 2 ^ k, 1⟩ = 1 := by
    have e1 : (⟨A ^ 2 ^ k, 1⟩ : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        ⋊[primeFormFieldU h hC1] (K ≃+* K)) = (⟨A, 1⟩ : primeFormUnitary h ((1 : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC1] (K ≃+* K)) ^ 2 ^ k := by
      rw [show (⟨A, 1⟩ : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          ⋊[primeFormFieldU h hC1] (K ≃+* K)) = SemidirectProduct.inl A from rfl, ← map_pow]
      rfl
    rw [e1, map_pow, hAφ, ← map_pow, hβk, map_one]
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h hC1 (by omega) _).1 hpow
  have hMk : M ^ 2 ^ k = scalar (Fin n) (c : K) := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
    simpa only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val,
      GeneralLinearGroup.coe_scalar] using this
  obtain ⟨j₀, hj₀⟩ : ∃ j, j ∉ ({a, b} : Finset (Fin n)) := by
    obtain ⟨j, hj⟩ := Finset.card_pos.1 (show 0 < ({a, b}ᶜ : Finset (Fin n)).card by omega)
    exact ⟨j, Finset.mem_compl.1 hj⟩
  have hNk : N ^ 2 ^ k = 1 := by
    have hNk' : N ^ 2 ^ k = scalar (Fin n) ((μ⁻¹) ^ 2 ^ k * c) := by
      rw [hNdef, smul_pow, hMk, scalar_apply, scalar_apply, ← diagonal_smul]
      rfl
    have hjj := LinearPilot.agrees_one_pow hN (2 ^ k) j₀ j₀ (Or.inl hj₀)
    rw [hNk', scalar_apply, diagonal_apply_eq, one_apply_eq] at hjj
    rw [hNk', hjj, map_one]
  have he := LinearPilot.pair_injective (n := n) hab
  have hJ := LinearPilot.mem_pair_iff_mem_range (a := a) (b := b)
  have hrowsN : ∀ i ∈ ({a, b} : Finset (Fin n)), ∀ l ∉ ({a, b} : Finset (Fin n)),
      N i l = 0 := fun i hi l hl => (LinearPilot.blockDiag_of_agrees_one hN) i l (by tauto)
  have hrowsY : ∀ i ∈ ({a, b} : Finset (Fin n)), ∀ l ∉ ({a, b} : Finset (Fin n)),
      Y i l = 0 := fun i hi l hl => LinearPilot.row_eq_zero_of_agrees_one hYa hi l hl
  have hblock : N.submatrix ![a, b] ![a, b] * Y.submatrix ![a, b] ![a, b] =
      Y.submatrix ![a, b] ![a, b] * N.submatrix ![a, b] ![a, b] := by
    rw [← LinearPilot.submatrix_mul_of_rows he hJ hrowsN,
      ← LinearPilot.submatrix_mul_of_rows he hJ hrowsY, hNy]
  have hdetY : Y.det = 1 := ((mem_unitarySU_iff h).1 y.2).1
  have hYY : Y * Y ≠ 1 := fun hYY => mul_self_ne_one_of_forall_pow_ne_one hyk
    (Subtype.ext (Units.ext (by rw [Subgroup.coe_mul, Units.val_mul]; exact hYY)))
  have hY0 := LinearPilot.not_scalar_submatrix_pair hab hYa hdetY hYY
  have hdet0 : (Y.submatrix ![a, b] ![a, b]).det = 1 := by
    rw [LinearPilot.det_submatrix_of_agrees_one he hJ hYa, hdetY]
  have hN0k : (N.submatrix ![a, b] ![a, b]) ^ 2 ^ k = 1 := by
    rw [← LinearPilot.submatrix_pow_of_agrees_one he hJ hN, hNk, submatrix_one _ he]
  rcases LinearPilot.eq_one_or_pow_eq_one_of_mul_eq_mul hY0 hdet0 hblock hN0k with h0 | h0
  ·
    have hN1 : N = 1 := LinearPilot.eq_one_of_agrees_one_of_submatrix_eq_one he hJ hN h0
    have hAs : (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) (Units.mk0 μ hμ0) := by
      apply Units.ext
      rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, scalar_apply, ← smul_one_eq_diagonal,
        ← hN1, hNdef, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
    have hΨ : primeFormPsi h hC1 ⟨A, 1⟩ = 1 :=
      (primeFormPsi_eq_one_iff h hC1 (by omega) _).2 ⟨rfl, Units.mk0 μ hμ0, hμN, hAs⟩
    rw [hΨ] at hAφ
    have := congrArg (MulAut.congr
      (CFSG.ComponentClassification.OutcomeLocal.primeFormOneEquiv h n).symm).symm hAφ
    rwa [map_one, MulEquiv.symm_apply_apply, eq_comm] at this
  ·
    exfalso
    apply hyk k
    have hYk : Y ^ 2 ^ k = 1 := LinearPilot.eq_one_of_agrees_one_of_submatrix_eq_one he hJ
      (LinearPilot.agrees_one_pow hYa _)
      (by rw [LinearPilot.submatrix_pow_of_agrees_one he hJ hYa, h0])
    exact Subtype.ext (Units.ext (by
      rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
      exact hYk))

end CFSG.SeitzReduction.UnitaryPilot

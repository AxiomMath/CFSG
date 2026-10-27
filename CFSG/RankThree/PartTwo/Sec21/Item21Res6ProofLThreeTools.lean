module

public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res6Proof

open Matrix CFSG CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

section Matrices

variable {K : Type} [Field K]

theorem mem_statedScalars_of_conj_diagTau [CharP K 2] {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {N : GL (Fin 3) K} {ℓ : Kˣ}
    (hN : N * Sec4.diagTau hτ * N⁻¹ = GeneralLinearGroup.scalar (Fin 3) ℓ * Sec4.diagTau hτ)
    (hN2 : N * N ∈ StatedScalars (Fin 3) K) : N ∈ StatedScalars (Fin 3) K := by
  obtain ⟨μ, hμ⟩ := hN2
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hcomm_scalar : ∀ (u : Kˣ) (M : GL (Fin 3) K),
      GeneralLinearGroup.scalar (Fin 3) u * M = M * GeneralLinearGroup.scalar (Fin 3) u := by
    intro u M
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  have hsq : (N * N) * Sec4.diagTau hτ * (N * N)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (ℓ * ℓ) * Sec4.diagTau hτ := by
    calc (N * N) * Sec4.diagTau hτ * (N * N)⁻¹ = N * (N * Sec4.diagTau hτ * N⁻¹) * N⁻¹ := by
          group
      _ = N * (GeneralLinearGroup.scalar (Fin 3) ℓ * Sec4.diagTau hτ) * N⁻¹ := by rw [hN]
      _ = GeneralLinearGroup.scalar (Fin 3) ℓ * (N * Sec4.diagTau hτ * N⁻¹) := by
          rw [← mul_assoc N, ← hcomm_scalar ℓ N]
          group
      _ = GeneralLinearGroup.scalar (Fin 3) (ℓ * ℓ) * Sec4.diagTau hτ := by
          rw [hN, ← mul_assoc, ← map_mul]
  have hsq' : (N * N) * Sec4.diagTau hτ * (N * N)⁻¹ = Sec4.diagTau hτ := by
    rw [← hμ, hcomm_scalar, mul_inv_cancel_right]
  have hℓ2 : ((ℓ : K) * ℓ) = 1 := by
    have h1 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 2 2)
      (hsq.symm.trans hsq')
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Sec4.coe_diagTau_eq_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] at h1
    simpa using h1
  have hℓ : (ℓ : K) = 1 := by
    have h2 : ((ℓ : K) + 1) * ((ℓ : K) + 1) = 0 := by
      have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination hℓ2 + ((ℓ : K) + 1) * h2'
    have h3 := mul_self_eq_zero.mp h2
    have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h3 - h2'
  have hℓ1 : ℓ = 1 := Units.ext hℓ
  rw [hℓ1, map_one, one_mul] at hN
  have hMδ : (N : Matrix (Fin 3) (Fin 3) K) * diagonal ![τ, τ ^ 2, 1] =
      diagonal ![τ, τ ^ 2, 1] * (N : Matrix (Fin 3) (Fin 3) K) := by
    have h1 : N * Sec4.diagTau hτ = Sec4.diagTau hτ * N := by
      calc N * Sec4.diagTau hτ = N * Sec4.diagTau hτ * N⁻¹ * N := by group
        _ = Sec4.diagTau hτ * N := by rw [hN]
    have h2 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K)) h1
    simp only [Units.val_mul, Sec4.coe_diagTau_eq_diagonal] at h2
    exact h2
  have h01 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have h' : τ * (τ - 1) = 0 := by linear_combination -h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hτ0)
  have h02 : τ ≠ 1 := hτ1
  have h12 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    linear_combination hτ - τ * h
  have hoff : ∀ i j : Fin 3, i ≠ j → (N : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro i j hij
    refine Sec4.entry_eq_zero_of_commute_diagonal hMδ ?_
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]
  have hdiag : ∀ i : Fin 3,
      (N : Matrix (Fin 3) (Fin 3) K) i i * (N : Matrix (Fin 3) (Fin 3) K) i i = μ := by
    intro i
    have h1 := congrArg (fun M' : GL (Fin 3) K => (M' : Matrix (Fin 3) (Fin 3) K) i i) hμ
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h1
    rw [h1, Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> simp [hoff]
  have hsq_inj : ∀ x y : K, x * x = y * y → x = y := by
    intro x y hxy
    have h1 : (x + y) * (x + y) = 0 := by
      have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination hxy + (x * y + y * y) * h2'
    have h3 := mul_self_eq_zero.mp h1
    linear_combination h3 - y * CharTwo.two_eq_zero (R := K)
  have heq : ∀ i : Fin 3, (N : Matrix (Fin 3) (Fin 3) K) i i = (N : Matrix (Fin 3) (Fin 3) K) 0 0 :=
    fun i => hsq_inj _ _ ((hdiag i).trans (hdiag 0).symm)
  have hM00 : (N : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h
    have h1 := hdiag 0
    rw [h, zero_mul] at h1
    exact μ.ne_zero h1.symm
  refine ⟨Units.mk0 ((N : Matrix (Fin 3) (Fin 3) K) 0 0) hM00, ?_⟩
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mk0]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, heq i]
  · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]

end Matrices

section Outer

theorem mem_inner_of_mem_commutator_of_mul_self {K : Type} [Field K] [Finite K]
    {σ : MulAut (projectiveSL 3 K)} (hσ : σ ∈ commutator (MulAut (projectiveSL 3 K)))
    (h2 : σ * σ = 1) : σ ∈ inner (projectiveSL 3 K) := by
  obtain ⟨N, -, hNcard, hNcomm⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.OuterDerived.exists_linear_outer_diagonal (K := K)
      (n := 3) le_rfl
  set π := QuotientGroup.mk' (inner (projectiveSL 3 K)) with hπ
  have hle : commutator (Outer (projectiveSL 3 K)) ≤ N := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    exact hNcomm a b
  have hπσ : π σ ∈ N := by
    apply hle
    have h1 : π σ ∈ (commutator (MulAut (projectiveSL 3 K))).map π := ⟨σ, hσ, rfl⟩
    rw [commutator_def, Subgroup.map_commutator] at h1
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top h1
  have hdvd3 : orderOf (π σ) ∣ 3 := by
    have h1 : orderOf (⟨π σ, hπσ⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact h1.trans (hNcard.trans (Nat.gcd_dvd_left 3 _))
  have hdvd2 : orderOf (π σ) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_two, ← map_mul, h2, map_one]
  have h0 : orderOf (π σ) ∣ Nat.gcd 2 3 := Nat.dvd_gcd hdvd2 hdvd3
  have h1 : orderOf (π σ) = 1 := Nat.dvd_one.mp (by rwa [show Nat.gcd 2 3 = 1 by norm_num] at h0)
  rw [orderOf_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem mem_inner_of_mulEquiv {Y Z : Type*} [Group Y] [Group Z] (φ : Y ≃* Z)
    (hZ : ∀ σ ∈ commutator (MulAut Z), σ * σ = 1 → σ ∈ inner Z) {σ : MulAut Y}
    (hσ : σ ∈ commutator (MulAut Y)) (h2 : σ * σ = 1) : σ ∈ inner Y := by
  set Φ : MulAut Y ≃* MulAut Z := MulAut.congr φ with hΦ
  have h1 : Φ σ ∈ commutator (MulAut Z) := by
    have h1 : Φ σ ∈ (commutator (MulAut Y)).map Φ.toMonoidHom := ⟨σ, hσ, rfl⟩
    rw [commutator_def, Subgroup.map_commutator] at h1
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top h1
  have h2' : Φ σ * Φ σ = 1 := by rw [← map_mul, h2, map_one]
  obtain ⟨z, hz⟩ := hZ _ h1 h2'
  refine ⟨φ.symm z, ?_⟩
  apply Φ.injective
  rw [← hz, hΦ, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj,
    MulEquiv.apply_symm_apply]

theorem mem_inner_of_mulEquiv_projSL {Y : Type*} [Group Y] {K : Type} [Field K] [Finite K]
    (e : Y ≃* CFSG.Assembly.RankThreeEven.projSL 3 K) {σ : MulAut Y}
    (hσ : σ ∈ commutator (MulAut Y)) (h2 : σ * σ = 1) : σ ∈ inner Y := by
  obtain ⟨φ⟩ := KFacts.nonempty_projSL_mulEquiv 3 K
  exact mem_inner_of_mulEquiv (e.trans φ) (fun τ hτ h => mem_inner_of_mem_commutator_of_mul_self
    hτ h) hσ h2

end Outer

end CFSG.RankThree.PartTwo.Sec21.Item21Res6Proof

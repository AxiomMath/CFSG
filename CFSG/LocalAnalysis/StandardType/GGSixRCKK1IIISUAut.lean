module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUCoord
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofAutSU

public section

namespace CFSG.StandardType.RCKK1IIISU

open Matrix CFSG.LieType.Universal.Unitary CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.RankFourTheoremC.AutSU

variable {k : ℕ}

private theorem rckSUa_card : Nat.card SUF = (2 ^ 1) ^ 2 := by
  show Nat.card (GaloisField 2 (2 * 1)) = (2 ^ 1) ^ 2
  rw [GaloisField.card 2 (2 * 1) (by norm_num)]
  norm_num

private theorem rckSUa_fieldData : UnitaryFieldData 2 1 SUF :=
  ⟨Nat.prime_two, le_refl 1, by rw [rckSUa_card, ← pow_mul, Nat.mul_comm]⟩

private theorem rckSUa_bar_apply (c : SUF) : rckSUa_fieldData.bar c = SUσ c := by
  rw [UnitaryFieldData.bar_apply, CFSG.LieType.BorelTits.unitaryInvolution_apply]

private theorem rckSUa_bar_eq : ⇑rckSUa_fieldData.bar = ⇑SUσ :=
  funext rckSUa_bar_apply

private noncomputable def rckSUa_witt (n : ℕ) : GL (Fin n) SUF :=
  (exists_wittMatrix rckSUa_card n).choose

private theorem rckSUa_witt_spec (n : ℕ) :
    conjTr SUσ (rckSUa_witt n : Matrix (Fin n) (Fin n) SUF) *
      (rckSUa_witt n : Matrix (Fin n) (Fin n) SUF) = antidiag n :=
  (exists_wittMatrix rckSUa_card n).choose_spec

private theorem rckSUa_bar_sigma_apply (τ : SUF ≃+* SUF) (x : SUF) :
    SUσ (τ x) = τ (SUσ x) := by
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply,
    CFSG.LieType.BorelTits.unitaryInvolution_apply, map_pow]

private theorem rckSUa_map_bar_sigma (M : Matrix (Fin k) (Fin k) SUF) (τ : SUF ≃+* SUF) :
    (M.map τ).map SUσ = (M.map SUσ).map τ := by
  rw [Matrix.map_map, Matrix.map_map]
  congr 1
  funext x
  exact rckSUa_bar_sigma_apply τ x

private theorem rckSUa_antidiag_map (n : ℕ) (τ : SUF ≃+* SUF) :
    (antidiag n).map τ = antidiag n := by
  ext i j
  simp only [Matrix.map_apply, antidiag, Matrix.of_apply]
  split_ifs <;> simp

private theorem rckSUa_antidiag_mul_self (n : ℕ) :
    antidiag n * antidiag n = (1 : Matrix (Fin n) (Fin n) SUF) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (Fin.rev i)]
  · by_cases h : j = i
    · subst h; simp [antidiag]
    · have h' : ¬ i = j := fun hij => h hij.symm
      simp [antidiag, h, h', Fin.rev_rev]
  · intro b _ hb
    simp [antidiag, hb]
  · intro h
    exact absurd (Finset.mem_univ (Fin.rev i)) h

private theorem rckSUa_map_inv {n : ℕ} (M : GL (Fin n) SUF) (τ : SUF ≃+* SUF) :
    ((M : Matrix (Fin n) (Fin n) SUF).map τ)⁻¹ =
      ((M⁻¹ : GL (Fin n) SUF) : Matrix (Fin n) (Fin n) SUF).map τ := by
  rw [← coe_glAut τ M, ← GeneralLinearGroup.coe_inv, ← (glAut τ).map_inv, coe_glAut]

private theorem rckSUa_mul_eq_of_mul_eq_one {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) SUF)
    (h : B * C = 1) : A * B * C * D = A * D := by
  rw [Matrix.mul_assoc A B C, h, Matrix.mul_one]

private noncomputable def rckSUa_conjSub {n : ℕ} (P : GL (Fin n) SUF)
    (hP : conjTr SUσ (P : Matrix (Fin n) (Fin n) SUF) * (P : Matrix (Fin n) (Fin n) SUF) =
      antidiag n) : SU SUσ n ≃* StatedSU n (2 ^ 1) SUF :=
  (conjEquiv P hP).trans (MulEquiv.subgroupCongr (SUid_eq_statedSU rckSUa_card n))

private theorem rckSUa_coe_conjSub {n : ℕ} (P : GL (Fin n) SUF)
    (hP : conjTr SUσ (P : Matrix (Fin n) (Fin n) SUF) * (P : Matrix (Fin n) (Fin n) SUF) =
      antidiag n) (g : SU SUσ n) :
    (((rckSUa_conjSub P hP) g : StatedSU n (2 ^ 1) SUF) : GL (Fin n) SUF) =
      P * (g : GL (Fin n) SUF) * P⁻¹ := by
  rw [rckSUa_conjSub, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, coe_conjEquiv]

private theorem rckSUa_coe_conjSub_symm {n : ℕ} (P : GL (Fin n) SUF)
    (hP : conjTr SUσ (P : Matrix (Fin n) (Fin n) SUF) * (P : Matrix (Fin n) (Fin n) SUF) =
      antidiag n) (y : StatedSU n (2 ^ 1) SUF) :
    (((rckSUa_conjSub P hP).symm y : SU SUσ n) : GL (Fin n) SUF) =
      P⁻¹ * (y : GL (Fin n) SUF) * P := by
  have h := rckSUa_coe_conjSub P hP ((rckSUa_conjSub P hP).symm y)
  rw [MulEquiv.apply_symm_apply] at h
  have h2 : P⁻¹ * (y : GL (Fin n) SUF) * P = (rckSUa_conjSub P hP).symm y := by
    rw [h]
    group
  exact h2.symm

theorem rckSU_aut (hk : 4 ≤ k) (α : MulAut (SUG k ⧸ Subgroup.center (SUG k))) :
    ∃ (τ : SUF ≃+* SUF) (B : GL (Fin k) SUF),
      conjTr SUσ (B : Matrix (Fin k) (Fin k) SUF) * antidiag k *
        (B : Matrix (Fin k) (Fin k) SUF) = antidiag k ∧
      ∀ g : SUG k, ∃ g' : SUG k,
        ((g' : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) =
          (B : Matrix (Fin k) (Fin k) SUF) *
            ((g : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map τ *
            ((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) ∧
        α (QuotientGroup.mk g) = QuotientGroup.mk g' := by
  obtain ⟨m, ε, hε, rfl⟩ : ∃ m ε, ε ≤ 1 ∧ k = 2 * m + ε :=
    ⟨k / 2, k % 2, by omega, by omega⟩
  have hm : 2 ≤ m := by omega
  have hn3 : 3 ≤ 2 * m + ε := by omega
  have hdq : (2 * m + ε, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have h3 : 2 * m + ε = 3 := (Prod.mk.inj h).1
    omega
  let n : ℕ := 2 * m + ε
  have hZ : Subgroup.center (StatedSU n (2 ^ 1) SUF) =
      (StatedScalars (Fin n) SUF).subgroupOf (StatedSU n (2 ^ 1) SUF) :=
    (isQuasisimple_statedSU_of_card (p := 2) (f := 1) rckSUa_card hn3 hdq).2
  let P : GL (Fin n) SUF := rckSUa_witt n
  have hP : conjTr SUσ (P : Matrix (Fin n) (Fin n) SUF) * (P : Matrix (Fin n) (Fin n) SUF) =
      antidiag n := rckSUa_witt_spec n
  let e₀ : SUG n ≃* StatedSU n (2 ^ 1) SUF := rckSUa_conjSub P hP
  have he : Subgroup.map (↑e₀) (Subgroup.center (SUG n)) =
      Subgroup.center (StatedSU n (2 ^ 1) SUF) := map_center_mulEquiv e₀
  let e : SUG n ⧸ Subgroup.center (SUG n) ≃* StatedProj (StatedSU n (2 ^ 1) SUF) :=
    (QuotientGroup.congr _ _ e₀ he).trans
      (QuotientGroup.quotientMulEquivOfEq hZ)
  have he_mk : ∀ g : SUG n, e (QuotientGroup.mk g) = QuotientGroup.mk (e₀ g) := by
    intro g
    change (QuotientGroup.quotientMulEquivOfEq hZ)
      ((QuotientGroup.congr _ _ e₀ he) (QuotientGroup.mk g)) =
        QuotientGroup.mk (e₀ g)
    rw [QuotientGroup.congr_mk, QuotientGroup.quotientMulEquivOfEq_mk]
  have he_symm_mk : ∀ y : StatedSU n (2 ^ 1) SUF,
      e.symm (QuotientGroup.mk y) = QuotientGroup.mk (e₀.symm y) := by
    intro y
    apply e.injective
    rw [MulEquiv.apply_symm_apply, he_mk, MulEquiv.apply_symm_apply]
  let γ : MulAut (StatedProj (StatedSU n (2 ^ 1) SUF)) := e.symm.trans (α.trans e)
  obtain ⟨σ, B_id, hB_id, hrep⟩ :=
    exists_isometry_of_mulAut_statedProj (p := 2) (f := 1) (m := m) (ε := ε)
      rckSUa_fieldData hm hε γ
  have hBid' : (((B_id : Matrix (Fin n) (Fin n) SUF)).map SUσ)ᵀ *
      (B_id : Matrix (Fin n) (Fin n) SUF) = 1 := by
    simpa only [rckSUa_bar_eq] using hB_id
  let Q : GL (Fin n) SUF := glAut SUσ P
  let R : GL (Fin n) SUF := glAut σ P
  let B : GL (Fin n) SUF := P⁻¹ * B_id * R
  have hγe : ∀ y, γ (e y) = e (α y) := by
    intro y
    simp only [γ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hBiso : conjTr SUσ (B : Matrix (Fin n) (Fin n) SUF) * antidiag n *
      (B : Matrix (Fin n) (Fin n) SUF) = antidiag n := by
    rw [conjTr]
    have hJmJm : antidiag n * antidiag n = (1 : Matrix (Fin n) (Fin n) SUF) :=
      rckSUa_antidiag_mul_self n
    have hQm : (Q : Matrix (Fin n) (Fin n) SUF) =
        (P : Matrix (Fin n) (Fin n) SUF).map SUσ := coe_glAut SUσ P
    have hRm : (R : Matrix (Fin n) (Fin n) SUF) =
        (P : Matrix (Fin n) (Fin n) SUF).map σ := coe_glAut σ P
    have hQmT : (Q : Matrix (Fin n) (Fin n) SUF)ᵀ * (P : Matrix (Fin n) (Fin n) SUF) =
        antidiag n := by
      rw [hQm]
      simpa only [conjTr] using rckSUa_witt_spec n
    have hQinv : ((Q : Matrix (Fin n) (Fin n) SUF)ᵀ)⁻¹ =
        (P : Matrix (Fin n) (Fin n) SUF) * antidiag n := by
      apply Matrix.inv_eq_right_inv
      rw [← Matrix.mul_assoc, hQmT, hJmJm]
    have hPP : (P : Matrix (Fin n) (Fin n) SUF) * (P : Matrix (Fin n) (Fin n) SUF)⁻¹ = 1 := by
      rw [← GeneralLinearGroup.coe_inv, ← GeneralLinearGroup.coe_mul, mul_inv_cancel,
        GeneralLinearGroup.coe_one]
    have hkey : ((Q : Matrix (Fin n) (Fin n) SUF)ᵀ)⁻¹ * antidiag n *
        (P : Matrix (Fin n) (Fin n) SUF)⁻¹ = 1 := by
      rw [hQinv]
      calc (P : Matrix (Fin n) (Fin n) SUF) * antidiag n * antidiag n *
            (P : Matrix (Fin n) (Fin n) SUF)⁻¹
          = (P : Matrix (Fin n) (Fin n) SUF) * (antidiag n * antidiag n) *
              (P : Matrix (Fin n) (Fin n) SUF)⁻¹ := by simp only [Matrix.mul_assoc]
        _ = (P : Matrix (Fin n) (Fin n) SUF) * (P : Matrix (Fin n) (Fin n) SUF)⁻¹ := by
              rw [hJmJm, Matrix.mul_one]
        _ = 1 := hPP
    have hBm : (B : Matrix (Fin n) (Fin n) SUF) =
        (P : Matrix (Fin n) (Fin n) SUF)⁻¹ * (B_id : Matrix (Fin n) (Fin n) SUF) *
          (R : Matrix (Fin n) (Fin n) SUF) := by
      simp only [B, GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_inv]
    have hBmap : (B : Matrix (Fin n) (Fin n) SUF).map SUσ =
        ((Q : Matrix (Fin n) (Fin n) SUF))⁻¹ *
          ((B_id : Matrix (Fin n) (Fin n) SUF).map SUσ) *
          (Q : Matrix (Fin n) (Fin n) SUF).map σ := by
      rw [hBm, ← GeneralLinearGroup.coe_inv P, Matrix.map_mul, Matrix.map_mul,
        ← rckSUa_map_inv P SUσ, ← hQm, hRm,
        rckSUa_map_bar_sigma (P : Matrix (Fin n) (Fin n) SUF) σ, ← hQm]
    rw [hBmap, hBm]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
    calc ((Q : Matrix (Fin n) (Fin n) SUF).map σ)ᵀ *
          (((B_id : Matrix (Fin n) (Fin n) SUF).map SUσ)ᵀ *
            ((Q : Matrix (Fin n) (Fin n) SUF)ᵀ)⁻¹) * antidiag n *
          ((P : Matrix (Fin n) (Fin n) SUF)⁻¹ * (B_id : Matrix (Fin n) (Fin n) SUF) *
            (R : Matrix (Fin n) (Fin n) SUF))
        = ((Q : Matrix (Fin n) (Fin n) SUF).map σ)ᵀ *
            ((B_id : Matrix (Fin n) (Fin n) SUF).map SUσ)ᵀ *
            (((Q : Matrix (Fin n) (Fin n) SUF)ᵀ)⁻¹ * antidiag n *
              (P : Matrix (Fin n) (Fin n) SUF)⁻¹) *
            (B_id : Matrix (Fin n) (Fin n) SUF) * (R : Matrix (Fin n) (Fin n) SUF) := by
          simp only [Matrix.mul_assoc]
      _ = ((Q : Matrix (Fin n) (Fin n) SUF).map σ)ᵀ *
            ((B_id : Matrix (Fin n) (Fin n) SUF).map SUσ)ᵀ * 1 *
            (B_id : Matrix (Fin n) (Fin n) SUF) * (R : Matrix (Fin n) (Fin n) SUF) := by
          rw [hkey]
      _ = ((Q : Matrix (Fin n) (Fin n) SUF).map σ)ᵀ *
            ((B_id : Matrix (Fin n) (Fin n) SUF).map SUσ)ᵀ *
            (B_id : Matrix (Fin n) (Fin n) SUF) * (R : Matrix (Fin n) (Fin n) SUF) := by
          rw [Matrix.mul_one]
      _ = ((Q : Matrix (Fin n) (Fin n) SUF).map σ)ᵀ * (R : Matrix (Fin n) (Fin n) SUF) :=
          rckSUa_mul_eq_of_mul_eq_one _ _ _ _ hBid'
      _ = ((Q : Matrix (Fin n) (Fin n) SUF).map σ)ᵀ *
            (P : Matrix (Fin n) (Fin n) SUF).map σ := by rw [hRm]
      _ = ((Q : Matrix (Fin n) (Fin n) SUF)ᵀ * (P : Matrix (Fin n) (Fin n) SUF)).map σ := by
          rw [← Matrix.transpose_map, Matrix.map_mul]
      _ = antidiag n := by rw [hQmT, rckSUa_antidiag_map]
  refine ⟨σ, B, hBiso, fun g => ?_⟩
  set x : StatedSU n (2 ^ 1) SUF := e₀ g with hx
  obtain ⟨hx_mem, hx_eq⟩ := hrep x
  set y : StatedSU n (2 ^ 1) SUF :=
    ⟨B_id * glAut σ (x : GL (Fin n) SUF) * B_id⁻¹, hx_mem⟩ with hy
  refine ⟨e₀.symm y, ?_, ?_⟩
  · have hxval : (x : GL (Fin n) SUF) = P * (g : GL (Fin n) SUF) * P⁻¹ := by
      rw [hx]; exact rckSUa_coe_conjSub P hP g
    have hyval : (y : GL (Fin n) SUF) =
        B_id * glAut σ (x : GL (Fin n) SUF) * B_id⁻¹ := rfl
    have hBinv : (B⁻¹ : GL (Fin n) SUF) = R⁻¹ * B_id⁻¹ * P := by
      show (P⁻¹ * B_id * R)⁻¹ = R⁻¹ * B_id⁻¹ * P
      group
    have hBm : (B : Matrix (Fin n) (Fin n) SUF) =
        (P : Matrix (Fin n) (Fin n) SUF)⁻¹ * (B_id : Matrix (Fin n) (Fin n) SUF) *
          (R : Matrix (Fin n) (Fin n) SUF) := by
      simp only [B, GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_inv]
    have hRm : (R : Matrix (Fin n) (Fin n) SUF) =
        (P : Matrix (Fin n) (Fin n) SUF).map σ := coe_glAut σ P
    rw [rckSUa_coe_conjSub_symm P hP y, hyval, hxval, hBinv, hBm]
    simp only [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_inv, coe_glAut,
      Matrix.map_mul]
    rw [hRm, ← GeneralLinearGroup.coe_inv P, ← rckSUa_map_inv P σ]
    simp only [Matrix.mul_assoc]
  · apply e.injective
    rw [← hγe (QuotientGroup.mk g), he_mk g, ← hx, hx_eq, he_mk (e₀.symm y),
      MulEquiv.apply_symm_apply]

end CFSG.StandardType.RCKK1IIISU

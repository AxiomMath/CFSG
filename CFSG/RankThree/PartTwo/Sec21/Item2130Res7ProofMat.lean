module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res6ProofMat

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130Res7Proof

open Matrix CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {K : Type} [Field K]

theorem diagUnits_inv (a b c : Kˣ) : (diagUnits a b c)⁻¹ = diagUnits a⁻¹ b⁻¹ c⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, diagUnits_mul]
  apply Units.ext
  rw [coe_diagUnits, Units.val_one, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem scalar_mul_diagUnits_normalize (l a b c : Kˣ) :
    GeneralLinearGroup.scalar (Fin 3) l * diagUnits a b c =
      GeneralLinearGroup.scalar (Fin 3) (l * a) * diagUnits 1 (b * a⁻¹) (c * a⁻¹) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
    coe_diagUnits, coe_diagUnits, Matrix.scalar_apply, Matrix.scalar_apply,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [mul_assoc] <;> field_simp

theorem scalar_mul_comm (l : Kˣ) (g : GL (Fin 3) K) :
    GeneralLinearGroup.scalar (Fin 3) l * g = g * GeneralLinearGroup.scalar (Fin 3) l :=
  (commute_of_mem_statedScalars ⟨l, rfl⟩ g).symm

theorem cycThree_conj_scalar_diag (l s t : Kˣ) :
    cycThree * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * cycThree⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (l * t) * diagUnits 1 (1 * t⁻¹) (s * t⁻¹) := by
  have hc : cycThree * GeneralLinearGroup.scalar (Fin 3) l =
      GeneralLinearGroup.scalar (Fin 3) l * cycThree := (scalar_mul_comm l cycThree).symm
  calc cycThree * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * cycThree⁻¹ =
      (cycThree * GeneralLinearGroup.scalar (Fin 3) l) * diagUnits 1 s t * cycThree⁻¹ := by
        group
    _ = (GeneralLinearGroup.scalar (Fin 3) l * cycThree) * diagUnits 1 s t * cycThree⁻¹ := by
        rw [hc]
    _ = GeneralLinearGroup.scalar (Fin 3) l * (cycThree * diagUnits 1 s t * cycThree⁻¹) := by
        group
    _ = GeneralLinearGroup.scalar (Fin 3) l * diagUnits t 1 s := by
        rw [cycThree_conj_diagUnits]
    _ = _ := scalar_mul_diagUnits_normalize l t 1 s

theorem cycThree_inv_conj_scalar_diag (l s t : Kˣ) :
    cycThree⁻¹ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * cycThree =
      GeneralLinearGroup.scalar (Fin 3) (l * s) * diagUnits 1 (t * s⁻¹) (1 * s⁻¹) := by
  have hc : cycThree⁻¹ * GeneralLinearGroup.scalar (Fin 3) l =
      GeneralLinearGroup.scalar (Fin 3) l * cycThree⁻¹ := (scalar_mul_comm l cycThree⁻¹).symm
  calc cycThree⁻¹ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * cycThree =
      (cycThree⁻¹ * GeneralLinearGroup.scalar (Fin 3) l) * diagUnits 1 s t * cycThree := by
        group
    _ = (GeneralLinearGroup.scalar (Fin 3) l * cycThree⁻¹) * diagUnits 1 s t * cycThree := by
        rw [hc]
    _ = GeneralLinearGroup.scalar (Fin 3) l * (cycThree⁻¹ * diagUnits 1 s t * cycThree) := by
        group
    _ = GeneralLinearGroup.scalar (Fin 3) l * diagUnits s t 1 := by
        rw [cycThree_inv_conj_diagUnits]
    _ = _ := scalar_mul_diagUnits_normalize l s t 1

variable {π : Bool} {p f : ℕ}

theorem exists_frame_of_type2 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {D : Subgroup (GL (Fin 3) K)} (hD : IsTypeC π (p ^ f) K D) {yc : GL (Fin 3) K}
    (hycD : yc ∈ D) (hycZ : yc ∉ StatedScalars (Fin 3) K) (h2 : Type123 π (p ^ f) K yc 2) :
    ∃ g ∈ glPi π 3 (p ^ f) K,
      (∀ a ∈ D, ∃ l s t : Kˣ, s ∈ rootsOfUnity 3 K ∧ t ∈ rootsOfUnity 3 K ∧
        g⁻¹ * a * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) ∧
      (∀ s ∈ rootsOfUnity 3 K, ∀ t ∈ rootsOfUnity 3 K, ∃ a ∈ D, ∃ l : Kˣ,
        g⁻¹ * a * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) ∧
      ∃ l σ : Kˣ, σ ∈ rootsOfUnity 3 K ∧ σ ≠ 1 ∧
        g⁻¹ * yc * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 σ σ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hcH : cycThree ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ (cycThree_mem_slPi hπ)
  obtain ⟨g, hgH, hdiag, hsurj⟩ := isTypeC_conj_std hK hq hD
  obtain ⟨lc, sc, tc, hsc, htc, hgc⟩ := hdiag yc hycD
  have htypes := type123_of_diag hK hq (hD.1 hycD) hgH hsc htc hgc
  have hnd : ¬ (sc ≠ 1 ∧ tc ≠ 1 ∧ sc ≠ tc) := fun h =>
    not_type123_one_two hK hq (htypes.1 h) h2
  have hnz : ¬ (sc = 1 ∧ tc = 1) := by
    rintro ⟨rfl, rfl⟩
    apply hycZ
    rw [← inv_conj_mem_statedScalars_iff g, hgc]
    exact (scalar_mul_diagUnits_mem_iff lc 1 1).mpr ⟨rfl, rfl⟩
  have hinv : ∀ u ∈ rootsOfUnity 3 K, u⁻¹ ∈ rootsOfUnity 3 K := fun u hu => inv_mem hu
  by_cases hs1 : sc = 1
  ·
    have ht1 : tc ≠ 1 := fun h => hnz ⟨hs1, h⟩
    have hconj : ∀ M : GL (Fin 3) K, (g * cycThree⁻¹)⁻¹ * M * (g * cycThree⁻¹) =
        cycThree * (g⁻¹ * M * g) * cycThree⁻¹ := fun M => by group
    refine ⟨g * cycThree⁻¹, mul_mem hgH (inv_mem hcH), fun a ha => ?_, fun s hs t ht => ?_,
      ⟨lc * tc, tc⁻¹, hinv tc htc, fun h => ht1 (inv_eq_one.mp h), ?_⟩⟩
    · obtain ⟨l, s, t, hs, ht, hl⟩ := hdiag a ha
      refine ⟨l * t, 1 * t⁻¹, s * t⁻¹, mul_mem (one_mem _) (hinv t ht),
        mul_mem hs (hinv t ht), ?_⟩
      rw [hconj, hl, cycThree_conj_scalar_diag]
    · obtain ⟨a, ha, l, hl⟩ := hsurj (t * s⁻¹) (mul_mem ht (hinv s hs)) s⁻¹ (hinv s hs)
      refine ⟨a, ha, l * s⁻¹, ?_⟩
      rw [hconj, hl, cycThree_conj_scalar_diag]
      simp only [one_mul, inv_inv, inv_mul_cancel_right]
    · rw [hconj, hgc, hs1, cycThree_conj_scalar_diag]
      simp only [one_mul]
  · by_cases ht1 : tc = 1
    ·
      have hconj : ∀ M : GL (Fin 3) K, (g * cycThree)⁻¹ * M * (g * cycThree) =
          cycThree⁻¹ * (g⁻¹ * M * g) * cycThree := fun M => by group
      refine ⟨g * cycThree, mul_mem hgH hcH, fun a ha => ?_, fun s hs t ht => ?_,
        ⟨lc * sc, sc⁻¹, hinv sc hsc, fun h => hs1 (inv_eq_one.mp h), ?_⟩⟩
      · obtain ⟨l, s, t, hs, ht, hl⟩ := hdiag a ha
        refine ⟨l * s, t * s⁻¹, 1 * s⁻¹, mul_mem ht (hinv s hs),
          mul_mem (one_mem _) (hinv s hs), ?_⟩
        rw [hconj, hl, cycThree_inv_conj_scalar_diag]
      · obtain ⟨a, ha, l, hl⟩ := hsurj t⁻¹ (hinv t ht) (s * t⁻¹) (mul_mem hs (hinv t ht))
        refine ⟨a, ha, l * t⁻¹, ?_⟩
        rw [hconj, hl, cycThree_inv_conj_scalar_diag]
        simp only [one_mul, inv_inv, inv_mul_cancel_right]
      · rw [hconj, hgc, ht1, cycThree_inv_conj_scalar_diag]
        simp only [one_mul]
    ·
      have hst : sc = tc := by
        by_contra h
        exact hnd ⟨hs1, ht1, h⟩
      exact ⟨g, hgH, hdiag, hsurj, lc, sc, hsc, hs1, by rw [hgc, hst]⟩

@[expose] def negSwap : GL (Fin 3) K :=
  ⟨!![-1, 0, 0; 0, 0, -1; 0, -1, 0], !![-1, 0, 0; 0, 0, -1; 0, -1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

theorem coe_negSwap :
    ((negSwap : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![-1, 0, 0; 0, 0, -1; 0, -1, 0] :=
  rfl

theorem coe_negSwap_inv :
    ((negSwap⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![-1, 0, 0; 0, 0, -1; 0, -1, 0] :=
  rfl

theorem negSwap_mem_slPi (q : ℕ) : negSwap ∈ slPi true 3 q K := by
  rw [mem_slPi_true, coe_negSwap, det_fin_three]
  simp

theorem negSwap_conj_diagUnits (a b c : Kˣ) :
    negSwap * diagUnits a b c * negSwap⁻¹ = diagUnits a c b := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_negSwap, coe_negSwap_inv, coe_diagUnits_eq,
    coe_diagUnits_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

theorem commutator_diagUnits_negSwap {σ : Kˣ} (hσ : σ ^ 3 = 1) :
    diagUnits 1 (σ ^ 2) σ * negSwap * (diagUnits 1 (σ ^ 2) σ)⁻¹ * negSwap⁻¹ =
      diagUnits 1 σ (σ ^ 2) := by
  rw [mul_assoc (diagUnits 1 (σ ^ 2) σ * negSwap), show diagUnits 1 (σ ^ 2) σ * negSwap *
    ((diagUnits 1 (σ ^ 2) σ)⁻¹ * negSwap⁻¹) =
      diagUnits 1 (σ ^ 2) σ * (negSwap * (diagUnits 1 (σ ^ 2) σ)⁻¹ * negSwap⁻¹) by group,
    diagUnits_inv, negSwap_conj_diagUnits, diagUnits_mul]
  have h1 : σ ^ 2 * σ⁻¹ = σ := by
    rw [pow_two, mul_inv_cancel_right]
  have h2 : σ * (σ ^ 2)⁻¹ = σ ^ 2 := by
    rw [mul_inv_eq_iff_eq_mul, ← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, hσ,
      one_mul, pow_one]
  rw [inv_one, mul_one, h1, h2]

theorem mul_apply_zero_zero_of_commute {P Q : Matrix (Fin 3) (Fin 3) K} {δ : Fin 3 → K}
    (h01 : δ 0 ≠ δ 1) (h02 : δ 0 ≠ δ 2) (hP : P * diagonal δ = diagonal δ * P) :
    (P * Q) 0 0 = P 0 0 * Q 0 0 := by
  have e01 : P 0 1 = 0 := Item2130Res6Proof.entry_eq_zero_of_commute_diagonal hP h01
  have e02 : P 0 2 = 0 := Item2130Res6Proof.entry_eq_zero_of_commute_diagonal hP h02
  rw [mul_apply, Fin.sum_univ_three, e01, e02, zero_mul, zero_mul, add_zero, add_zero]

theorem commute_diagonal_inv {N : GL (Fin 3) K} {δ : Fin 3 → K}
    (h : (N : Matrix (Fin 3) (Fin 3) K) * diagonal δ = diagonal δ * N) :
    ((N⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal δ =
      diagonal δ * ((N⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have hN : ((N⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * N = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hN' : (N : Matrix (Fin 3) (Fin 3) K) * ((N⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  set Ni := ((N⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hNi
  calc Ni * diagonal δ = Ni * diagonal δ * ((N : Matrix (Fin 3) (Fin 3) K) * Ni) := by
        rw [hN', Matrix.mul_one]
    _ = Ni * (diagonal δ * N) * Ni := by simp only [Matrix.mul_assoc]
    _ = Ni * (N * diagonal δ) * Ni := by rw [← h]
    _ = (Ni * N) * diagonal δ * Ni := by simp only [Matrix.mul_assoc]
    _ = diagonal δ * Ni := by rw [hN, Matrix.one_mul]

theorem entry_commutator_eq_one {N₁ N₂ : GL (Fin 3) K} {δ : Fin 3 → K} (h01 : δ 0 ≠ δ 1)
    (h02 : δ 0 ≠ δ 2) (h₁ : (N₁ : Matrix (Fin 3) (Fin 3) K) * diagonal δ = diagonal δ * N₁)
    (h₂ : (N₂ : Matrix (Fin 3) (Fin 3) K) * diagonal δ = diagonal δ * N₂) :
    ((N₁ * N₂ * N₁⁻¹ * N₂⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
  have h₁' := commute_diagonal_inv h₁
  have h₂' := commute_diagonal_inv h₂
  have hmul : ∀ {P Q : Matrix (Fin 3) (Fin 3) K}, P * diagonal δ = diagonal δ * P →
      Q * diagonal δ = diagonal δ * Q → (P * Q) * diagonal δ = diagonal δ * (P * Q) := by
    intro P Q hP hQ
    rw [Matrix.mul_assoc, hQ, ← Matrix.mul_assoc, hP, Matrix.mul_assoc]
  have e : ∀ N : GL (Fin 3) K, (N : Matrix (Fin 3) (Fin 3) K) * diagonal δ = diagonal δ * N →
      (N : Matrix (Fin 3) (Fin 3) K) 0 0 * ((N⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 =
        1 := by
    intro N hN
    rw [← mul_apply_zero_zero_of_commute h01 h02 hN, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_apply_eq]
  rw [Units.val_mul, Units.val_mul, Units.val_mul,
    mul_apply_zero_zero_of_commute h01 h02 (hmul (hmul h₁ h₂) h₁'),
    mul_apply_zero_zero_of_commute h01 h02 (hmul h₁ h₂),
    mul_apply_zero_zero_of_commute h01 h02 h₁]
  linear_combination (((N₂ : Matrix (Fin 3) (Fin 3) K) 0 0 *
      ((N₂⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0)) * (e N₁ h₁) + e N₂ h₂

end CFSG.RankThree.PartTwo.Sec21.Item2130Res7Proof

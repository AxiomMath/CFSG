module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofGU2
public import CFSG.LieType.SeitzGeneration.UnitaryHeisHom

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGLU27

open scoped MatrixGroups

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem su2_conj_mem_prim (h : UnitaryFieldData ℓ f K)
    (hq4 : 4 ≤ ℓ ^ f) (H : Subgroup (GL (Fin 3) K)) (P : GL (Fin 3) K)
    {μ₁ μ₂ ν₁ ν₂ α β : K} (hμ₁ : h.bar μ₁ * μ₁ = 1) (hμ₂ : h.bar μ₂ * μ₂ = 1)
    (hν₁ : h.bar ν₁ * ν₁ = 1) (hν₂ : h.bar ν₂ * ν₂ = 1) (hαβ : h.bar α * α + h.bar β * β = 1)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hμ6 : 6 ≤ orderOf (μ₁ / μ₂))
    (hsf : SubfieldFree ℓ f (orderOf (μ₁ / μ₂))) (hν3 : 3 ≤ orderOf (ν₁ / ν₂))
    {A B : GL (Fin 2) K}
    (hAm : (A : Matrix (Fin 2) (Fin 2) K) = diagonal ![μ₁, μ₂])
    (hBm : (B : Matrix (Fin 2) (Fin 2) K) =
      !![ν₂ + (ν₁ - ν₂) * (α * h.bar α), (ν₁ - ν₂) * (α * h.bar β);
        (ν₁ - ν₂) * (β * h.bar α), ν₂ + (ν₁ - ν₂) * (β * h.bar β)])
    (hA : P * blockDetGL A * P⁻¹ ∈ H) (hB : P * blockDetGL B * P⁻¹ ∈ H) :
    ∀ g : GL (Fin 2) K, g ∈ unitarySU ℓ f K 2 → P * blockDetGL g * P⁻¹ ∈ H := by
  intro g hg
  exact su2_le_of_pair_prim h hq4
    (H.comap ((MulAut.conj P).toMonoidHom.comp blockDetGL)) hμ₁ hμ₂ hν₁ hν₂ hαβ hα hβ hμ6 hsf hν3
    hAm hBm hA hB g hg

theorem su2_block_mem_of_generic_prim
    (h : UnitaryFieldData ℓ f K) (hq4 : 4 ≤ ℓ ^ f) {a : K} (haq : a ^ (ℓ ^ f + 1) = 1)
    (ha3 : 3 ≤ orderOf a) (h6 : 6 ≤ orderOf (a⁻¹ ^ 2 / a))
    (hsf : SubfieldFree ℓ f (orderOf (a⁻¹ ^ 2 / a))) (H : Subgroup (GL (Fin 3) K))
    (hH1 : ∃ g ∈ H, (g : Matrix (Fin 3) (Fin 3) K) = homMat h a (a⁻¹ ^ 2 - a) ![1, 0, 0])
    (hH3 : ∃ g ∈ H, (g : Matrix (Fin 3) (Fin 3) K) = homMat h a (a⁻¹ ^ 2 - a) ![0, 0, 1])
    {w : Fin 3 → K} (hw : h.bar (w 0) * w 0 + h.bar (w 1) * w 1 + h.bar (w 2) * w 2 = 1)
    (hw0 : w 0 ≠ 0) (hw1 : w 1 ≠ 0) (hw2 : w 2 ≠ 0)
    (hnz : h.bar (w 0) * w 0 + h.bar (w 1) * w 1 ≠ 0)
    (hHw : ∃ g ∈ H, (g : Matrix (Fin 3) (Fin 3) K) = homMat h a (a⁻¹ ^ 2 - a) w) :
    ∀ g : GL (Fin 2) K, g ∈ unitarySU ℓ f K 2 → blockOneGL g ∈ H := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := h.card_eq_sq
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at haq
    exact zero_ne_one haq
  have hna : h.bar a * a = 1 := by
    rw [bar_mul_self_eq_pow]
    exact haq
  have hlam : a⁻¹ ^ 2 * a * a = 1 := by field_simp
  have hlamN : h.bar (a⁻¹ ^ 2) * a⁻¹ ^ 2 = 1 := by
    rw [map_pow, map_inv₀, ← mul_pow, ← mul_inv, hna, inv_one, one_pow]
  set d : K := h.bar (w 0) * w 0 + h.bar (w 1) * w 1 with hd
  have hdfix : h.bar d = d := by
    rw [hd, map_add, map_mul, map_mul, h.bar_bar, h.bar_bar]
    ring
  obtain ⟨c, hc⟩ : ∃ c : K, h.bar c * c = d := by
    have hfix : CFSG.LieType.BorelTits.unitaryInvolution K ℓ f d = d := by
      rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h.bar_apply]
      exact hdfix
    obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed (p := ℓ) (f := f) hK
      hfix hnz
    refine ⟨c, ?_⟩
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h.bar_apply] at hc
    exact hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hnz
    rw [← hc]
    simp
  have hbc : h.bar c ≠ 0 := by simpa using hc0
  have hαβ' : h.bar (w 0 / c) * (w 0 / c) + h.bar (w 1 / c) * (w 1 / c) = 1 := by
    rw [map_div₀, map_div₀]
    field_simp
    linear_combination -hc
  set α' : K := w 0 / c with hα'
  set β' : K := w 1 / c with hβ'
  have hα'0 : α' ≠ 0 := div_ne_zero hw0 hc0
  have hβ'0 : β' ≠ 0 := div_ne_zero hw1 hc0
  have hαc : c * α' = w 0 := by rw [hα']; field_simp
  have hβc : c * β' = w 1 := by rw [hβ']; field_simp
  set P₁ : GL (Fin 3) K := frameGL h hαβ' with hP₁
  have hαβ1 : h.bar (w 2) * w 2 + h.bar c * c = 1 := by
    rw [hc]
    linear_combination hw
  have hdiag0 : (diagonal ![a⁻¹ ^ 2, a] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_two, ha0]
  have hdetB : (!![a + (a⁻¹ ^ 2 - a) * (w 2 * h.bar (w 2)), (a⁻¹ ^ 2 - a) * (w 2 * h.bar c);
      (a⁻¹ ^ 2 - a) * (c * h.bar (w 2)), a + (a⁻¹ ^ 2 - a) * (c * h.bar c)] :
      Matrix (Fin 2) (Fin 2) K).det = a⁻¹ ^ 2 * a := by
    rw [Matrix.det_fin_two_of]
    linear_combination (a * (a⁻¹ ^ 2 - a)) * hαβ1
  have hdetB0 : (!![a + (a⁻¹ ^ 2 - a) * (w 2 * h.bar (w 2)), (a⁻¹ ^ 2 - a) * (w 2 * h.bar c);
      (a⁻¹ ^ 2 - a) * (c * h.bar (w 2)), a + (a⁻¹ ^ 2 - a) * (c * h.bar c)] :
      Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [hdetB]
    exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero ha0)) ha0
  let A₁ : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal ![a⁻¹ ^ 2, a]) hdiag0
  let B₁ : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![a + (a⁻¹ ^ 2 - a) * (w 2 * h.bar (w 2)), (a⁻¹ ^ 2 - a) * (w 2 * h.bar c);
      (a⁻¹ ^ 2 - a) * (c * h.bar (w 2)), a + (a⁻¹ ^ 2 - a) * (c * h.bar c)] hdetB0
  have hPstar : ((P₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = frameMat h α' β' := rfl
  have hPinv : ((P₁⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((frameMat h α' β').map h.bar)ᵀ := rfl
  have hv1 : frameMat h α' β' *ᵥ ![1, 0, 0] = ![0, 0, 1] := by
    rw [frameMat_mulVec]
    simp
  have hS1 : ∀ g : GL (Fin 2) K, g ∈ unitarySU ℓ f K 2 → P₁ * blockDetGL g * P₁⁻¹ ∈ H := by
    refine su2_conj_mem_prim h hq4 H P₁ hlamN hna hlamN hna hαβ1 hw2 hc0 h6 hsf (by omega)
      (A := A₁) (B := B₁) rfl rfl ?_ ?_
    · obtain ⟨g, hg, hgm⟩ := hH3
      have : P₁ * blockDetGL A₁ * P₁⁻¹ = g := by
        apply Units.ext
        rw [hgm, Units.val_mul, Units.val_mul, hPstar, hPinv, coe_blockDetGL]
        change frameMat h α' β' * blockDetMat (diagonal ![a⁻¹ ^ 2, a]) * _ = _
        rw [blockDetMat_diagonal h hlam, conj_homMat h _ (frameMat_mul_star h hαβ'), hv1]
      rw [this]
      exact hg
    · obtain ⟨g, hg, hgm⟩ := hHw
      have : P₁ * blockDetGL B₁ * P₁⁻¹ = g := by
        apply Units.ext
        rw [hgm, Units.val_mul, Units.val_mul, hPstar, hPinv, coe_blockDetGL]
        change frameMat h α' β' *
          blockDetMat !![a + (a⁻¹ ^ 2 - a) * (w 2 * h.bar (w 2)), (a⁻¹ ^ 2 - a) * (w 2 * h.bar c);
            (a⁻¹ ^ 2 - a) * (c * h.bar (w 2)), a + (a⁻¹ ^ 2 - a) * (c * h.bar c)] * _ = _
        rw [blockDetMat_homology h hαβ1 hlam, conj_homMat h _ (frameMat_mul_star h hαβ'),
          frameMat_mulVec]
        have hvw : (![c * α', c * β', w 2] : Fin 3 → K) = w := by
          ext i
          fin_cases i <;> simp [hαc, hβc]
        rw [hvw]
      rw [this]
      exact hg
  have hxa : (!![1 + (a - 1) * (α' * h.bar α'), (a - 1) * (α' * h.bar β');
      (a - 1) * (β' * h.bar α'), 1 + (a - 1) * (β' * h.bar β')] :
      Matrix (Fin 2) (Fin 2) K).det = a := by
    rw [Matrix.det_fin_two_of]
    linear_combination (a - 1) * hαβ'
  have hxa0 : (!![1 + (a - 1) * (α' * h.bar α'), (a - 1) * (α' * h.bar β');
      (a - 1) * (β' * h.bar α'), 1 + (a - 1) * (β' * h.bar β')] :
      Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [hxa]
    exact ha0
  let B₂ : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![1 + (a - 1) * (α' * h.bar α'), (a - 1) * (α' * h.bar β');
      (a - 1) * (β' * h.bar α'), 1 + (a - 1) * (β' * h.bar β')] hxa0
  have hD0 : (diagonal ![a⁻¹, a] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_two, ha0]
  let D₁ : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal ![a⁻¹, a]) hD0
  have hD₁ : D₁ ∈ unitarySU ℓ f K 2 := by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · show (diagonal ![a⁻¹, a] : Matrix (Fin 2) (Fin 2) K).det = 1
      simp [Matrix.det_diagonal, Fin.prod_univ_two, ha0]
    · show ((diagonal ![a⁻¹, a] : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * diagonal ![a⁻¹, a] = 1
      have hbi : (h.bar a)⁻¹ * a⁻¹ = 1 := by
        rw [← mul_inv, hna, inv_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hbi, hna]
  have hS2 : ∀ g : GL (Fin 2) K, g ∈ unitarySU ℓ f K 2 → 1 * blockDetGL g * 1⁻¹ ∈ H := by
    refine su2_conj_mem_prim h hq4 H 1 hlamN hna hna (by simp) hαβ' hα'0 hβ'0 h6 hsf
      (by rw [div_one]; exact ha3) (A := A₁) (B := B₂) rfl rfl ?_ ?_
    · obtain ⟨g, hg, hgm⟩ := hH1
      have : 1 * blockDetGL A₁ * 1⁻¹ = g := by
        apply Units.ext
        rw [hgm, one_mul, inv_one, mul_one, coe_blockDetGL]
        exact blockDetMat_diagonal h hlam
      rw [this]
      exact hg
    · have hmem := hS1 D₁ hD₁
      have : 1 * blockDetGL B₂ * 1⁻¹ = P₁ * blockDetGL D₁ * P₁⁻¹ := by
        rw [one_mul, inv_one, mul_one]
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, hPstar, hPinv, coe_blockDetGL, coe_blockDetGL]
        change _ = frameMat h α' β' * blockDetMat (diagonal ![a⁻¹, a]) * _
        rw [frame_conj_diagonal h hαβ' ha0]
        rfl
      rw [this]
      exact hmem
  intro g hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) K).det = 1 := ((mem_unitarySU_iff h).1 hg).1
  have := hS2 g hg
  rw [blockDetGL_eq_blockOneGL hdet, one_mul, inv_one, mul_one] at this
  exact this

end CFSG.RankThree.PartTwo.Sec14.L3PGLU27

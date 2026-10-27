module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeafBIdem
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeafBUnit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {f : ℕ} {ψ : Su K 2 f 6 →* G}

private lemma ggNSPosPF3C_unitaryInvolution_omega {ω : K} (hω : IsPrimitiveRoot ω 3)
    (hdvd : 3 ∣ 2 ^ f + 1) : unitaryInvolution K 2 f ω = ω ^ 2 := by
  obtain ⟨k, hk⟩ := hdvd
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hωω : ω * ω ^ 2 = 1 := by
    have : ω * ω ^ 2 = ω ^ 3 := by ring
    rw [this, hω3]
  have h1 : ω ^ 2 ^ f * ω = 1 := by
    rw [← pow_succ, hk, pow_mul, hω3, one_pow]
  rw [unitaryInvolution_apply]
  calc ω ^ 2 ^ f = ω ^ 2 ^ f * 1 := (mul_one _).symm
    _ = ω ^ 2 ^ f * (ω * ω ^ 2) := by rw [hωω]
    _ = (ω ^ 2 ^ f * ω) * ω ^ 2 := by rw [mul_assoc]
    _ = 1 * ω ^ 2 := by rw [h1]
    _ = ω ^ 2 := one_mul _

theorem ggNSPosPF3C_exists_shearData (h : GGNSLocalHyp 3 B Bs K f 6 ψ) {ω : K}
    (hω : IsPrimitiveRoot ω 3) {X Y N : GL (Fin 6) K} (hX3 : X ^ 3 = 1)
    (hYX : (Y : Matrix (Fin 6) (Fin 6) K) * (X : Matrix (Fin 6) (Fin 6) K) =
      ω • ((X : Matrix (Fin 6) (Fin 6) K) * (Y : Matrix (Fin 6) (Fin 6) K)))
    (hNX : (N : Matrix (Fin 6) (Fin 6) K) * (X : Matrix (Fin 6) (Fin 6) K) =
      (X : Matrix (Fin 6) (Fin 6) K) * (N : Matrix (Fin 6) (Fin 6) K))
    (hNY : (N : Matrix (Fin 6) (Fin 6) K) * (Y : Matrix (Fin 6) (Fin 6) K) =
      (Y : Matrix (Fin 6) (Fin 6) K) * (N : Matrix (Fin 6) (Fin 6) K))
    (hNns : ¬ ∃ s : K, (N : Matrix (Fin 6) (Fin 6) K) = s • 1)
    (hXlift : ∃ b ∈ Bs, ∃ (g : GL (Fin 6) K) (t : Kˣ),
      GGInducesUnitary (p := 2) (f := f) ψ b g ∧
        X = g * Matrix.GeneralLinearGroup.scalar (Fin 6) t)
    (hNlift : ∃ b ∈ Bs, ∃ (g : GL (Fin 6) K) (t : Kˣ),
      GGInducesUnitary (p := 2) (f := f) ψ b g ∧
        N = g * Matrix.GeneralLinearGroup.scalar (Fin 6) t)
    {τ : K} (hτ : τ ≠ 0)
    (hNq : (N : Matrix (Fin 6) (Fin 6) K) * (N : Matrix (Fin 6) (Fin 6) K) =
      τ • (N : Matrix (Fin 6) (Fin 6) K) + τ ^ 2 • 1) :
    ∃ c : GL (Fin 6) K,
      ggNSPosPF3C_ShearData (unitaryInvolution K 2 f) ω X Y c ∧
        (∃ b ∈ Bs, GGInducesUnitary (p := 2) (f := f) ψ b X) ∧
        ∃ b ∈ Bs, GGInducesUnitary (p := 2) (f := f) ψ b c := by
  have hω' : ω ^ 2 + ω + 1 = 0 := by
    have hsum := hω.geom_sum_eq_zero (k := 3) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at hsum
    have : ω ^ 2 + ω + 1 = 1 + ω + ω ^ 2 := by abel
    rw [this]
    exact hsum
  have hω_ne : ω ≠ 0 := hω.ne_zero (by norm_num)
  have hσω : unitaryInvolution K 2 f ω = ω ^ 2 :=
    ggNSPosPF3C_unitaryInvolution_omega hω h.dvd
  have hτω : τ * ω ≠ 0 := mul_ne_zero hτ hω_ne
  obtain ⟨bX, hbX, gX, tX, hgX, hXeq⟩ := hXlift
  have hXun : GGInducesUnitary (p := 2) (f := f) ψ bX X := by
    have h3 : (gX * Matrix.GeneralLinearGroup.scalar (Fin 6) tX) ^ 3 = 1 := by
      rw [← hXeq, hX3]
    have := ggNSPosPF3C_lift_mul_scalar_of_pow_three h hgX tX h3
    rwa [← hXeq] at this
  let c : GL (Fin 6) K := Matrix.GeneralLinearGroup.scalar (Fin 6)
    (Units.mk0 ((τ * ω)⁻¹) (inv_ne_zero hτω)) * N
  have hcdef : c = Matrix.GeneralLinearGroup.scalar (Fin 6)
      (Units.mk0 ((τ * ω)⁻¹) (inv_ne_zero hτω)) * N := rfl
  have hcval : (c : Matrix (Fin 6) (Fin 6) K) =
      (τ * ω)⁻¹ • (N : Matrix (Fin 6) (Fin 6) K) := by
    rw [hcdef, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  have hNm : (N : Matrix (Fin 6) (Fin 6) K) =
      (τ * ω) • (c : Matrix (Fin 6) (Fin 6) K) := by
    rw [hcval, smul_smul, mul_inv_cancel₀ hτω, one_smul]
  have hcX : (c : Matrix (Fin 6) (Fin 6) K) * (X : Matrix (Fin 6) (Fin 6) K) =
      (X : Matrix (Fin 6) (Fin 6) K) * (c : Matrix (Fin 6) (Fin 6) K) := by
    rw [hcval, Matrix.smul_mul, Matrix.mul_smul, ← hNX]
  have hcY : (c : Matrix (Fin 6) (Fin 6) K) * (Y : Matrix (Fin 6) (Fin 6) K) =
      (Y : Matrix (Fin 6) (Fin 6) K) * (c : Matrix (Fin 6) (Fin 6) K) := by
    rw [hcval, Matrix.smul_mul, Matrix.mul_smul, ← hNY]
  have hω_inv : ω⁻¹ = ω ^ 2 := inv_eq_of_mul_eq_one_right (by
    have : ω * ω ^ 2 = ω ^ 3 := by ring
    rw [this, hω.pow_eq_one])
  have hs : (τ * ω)⁻¹ = ω ^ 2 * τ⁻¹ := by rw [_root_.mul_inv_rev, hω_inv]
  have h1 : ((τ * ω)⁻¹ * (τ * ω)⁻¹) * τ = ω ^ 2 * (τ * ω)⁻¹ := by
    rw [hs]
    field_simp
  have h2 : ((τ * ω)⁻¹ * (τ * ω)⁻¹) * τ ^ 2 = ω := by
    rw [hs]
    field_simp
    exact hω.pow_eq_one
  have hcquad : (c : Matrix (Fin 6) (Fin 6) K) * (c : Matrix (Fin 6) (Fin 6) K) =
      ω ^ 2 • (c : Matrix (Fin 6) (Fin 6) K) +
        ω • (1 : Matrix (Fin 6) (Fin 6) K) := by
    rw [hcval, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hNq, smul_add, smul_smul,
      smul_smul, smul_smul, h1, h2]
  have hcns : ∀ a : K, (c : Matrix (Fin 6) (Fin 6) K) ≠ a • 1 := by
    intro a ha
    apply hNns
    refine ⟨(τ * ω) * a, ?_⟩
    rw [hNm, ha, smul_smul]
  obtain ⟨bN, hbN, gN, tN, hgN, hNeq⟩ := hNlift
  have hceq : c = gN * Matrix.GeneralLinearGroup.scalar (Fin 6)
      (Units.mk0 ((τ * ω)⁻¹) (inv_ne_zero hτω) * tN) := by
    show Matrix.GeneralLinearGroup.scalar (Fin 6)
        (Units.mk0 ((τ * ω)⁻¹) (inv_ne_zero hτω)) * N =
      gN * Matrix.GeneralLinearGroup.scalar (Fin 6)
        (Units.mk0 ((τ * ω)⁻¹) (inv_ne_zero hτω) * tN)
    rw [hNeq, ← mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, mul_assoc, ← map_mul]
  have hc3 : c ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact ggNSPosPF3C_pow_three hω' hcquad
  have hcun : GGInducesUnitary (p := 2) (f := f) ψ bN c := by
    have h3 : (gN * Matrix.GeneralLinearGroup.scalar (Fin 6)
        (Units.mk0 ((τ * ω)⁻¹) (inv_ne_zero hτω) * tN)) ^ 3 = 1 := by
      rw [← hceq, hc3]
    have := ggNSPosPF3C_lift_mul_scalar_of_pow_three h hgN
      (Units.mk0 ((τ * ω)⁻¹) (inv_ne_zero hτω) * tN) h3
    rwa [← hceq] at this
  refine ⟨c, ?_, ⟨bX, hbX, hXun⟩, ⟨bN, hbN, hcun⟩⟩
  refine ⟨hω', hσω, hX3, hXun.1, hcun.1, hYX, hcX, hcY, hcquad, hcns⟩

end CFSG.StandardType

end

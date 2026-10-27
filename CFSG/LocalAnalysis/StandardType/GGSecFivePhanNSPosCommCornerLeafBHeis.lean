module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosLiftE
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeafBCount
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLLift
import CFSG.RankThree.PartOne.CTP.SeitzDiag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {f : ℕ} {ψ : Su K 2 f 6 →* G}

private lemma ggNSPosPF3C_conj_mul_scalar (g X : GL (Fin 6) K) (t : Kˣ) :
    (g * Matrix.GeneralLinearGroup.scalar (Fin 6) t) * X *
        (g * Matrix.GeneralLinearGroup.scalar (Fin 6) t)⁻¹ = g * X * g⁻¹ := by
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin 6) t * X *
      (Matrix.GeneralLinearGroup.scalar (Fin 6) t)⁻¹ = X := by
    rw [Matrix.GeneralLinearGroup.scalar_commute t X]
    group
  calc (g * Matrix.GeneralLinearGroup.scalar (Fin 6) t) * X *
        (g * Matrix.GeneralLinearGroup.scalar (Fin 6) t)⁻¹
      = g * (Matrix.GeneralLinearGroup.scalar (Fin 6) t * X *
          (Matrix.GeneralLinearGroup.scalar (Fin 6) t)⁻¹) * g⁻¹ := by group
    _ = g * X * g⁻¹ := by rw [hsc]

private lemma ggNSPosPF3C_mul_scalar_comm (g N : GL (Fin 6) K) (t : Kˣ)
    (h : N * (g * Matrix.GeneralLinearGroup.scalar (Fin 6) t) =
      (g * Matrix.GeneralLinearGroup.scalar (Fin 6) t) * N) :
    N * g = g * N := by
  have h' : N * g * Matrix.GeneralLinearGroup.scalar (Fin 6) t =
      g * N * Matrix.GeneralLinearGroup.scalar (Fin 6) t := by
    calc N * g * Matrix.GeneralLinearGroup.scalar (Fin 6) t
        = N * (g * Matrix.GeneralLinearGroup.scalar (Fin 6) t) := by rw [mul_assoc]
      _ = (g * Matrix.GeneralLinearGroup.scalar (Fin 6) t) * N := h
      _ = g * (Matrix.GeneralLinearGroup.scalar (Fin 6) t * N) := by rw [mul_assoc]
      _ = g * (N * Matrix.GeneralLinearGroup.scalar (Fin 6) t) := by
            rw [Matrix.GeneralLinearGroup.scalar_commute t N]
      _ = g * N * Matrix.GeneralLinearGroup.scalar (Fin 6) t := by rw [mul_assoc]
  exact mul_right_cancel h'

theorem ggNSPosPF3C_heisenberg_data (h : GGNSLocalHyp 3 B Bs K f 6 ψ) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ Bs) (hb₂ : b₂ ∈ Bs) {g₁ g₂ : GL (Fin 6) K}
    (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b₁ g₁)
    (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b₂ g₂) (hne : g₁ * g₂ ≠ g₂ * g₁) :
    ∃ (ω : K) (X Y N : GL (Fin 6) K), IsPrimitiveRoot ω 3 ∧ X ^ 3 = 1 ∧
      (Y : Matrix (Fin 6) (Fin 6) K) * (X : Matrix (Fin 6) (Fin 6) K) =
        ω • ((X : Matrix (Fin 6) (Fin 6) K) * (Y : Matrix (Fin 6) (Fin 6) K)) ∧
      (N : Matrix (Fin 6) (Fin 6) K) * (X : Matrix (Fin 6) (Fin 6) K) =
        (X : Matrix (Fin 6) (Fin 6) K) * (N : Matrix (Fin 6) (Fin 6) K) ∧
      (N : Matrix (Fin 6) (Fin 6) K) * (Y : Matrix (Fin 6) (Fin 6) K) =
        (Y : Matrix (Fin 6) (Fin 6) K) * (N : Matrix (Fin 6) (Fin 6) K) ∧
      (∃ s : K, ((N ^ 3 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = s • 1) ∧
      (¬ ∃ s : K, (N : Matrix (Fin 6) (Fin 6) K) = s • 1) ∧
      (∃ b ∈ Bs, ∃ (g : GL (Fin 6) K) (t : Kˣ),
        GGInducesUnitary (p := 2) (f := f) ψ b g ∧
          X = g * Matrix.GeneralLinearGroup.scalar (Fin 6) t) ∧
      (∃ b ∈ Bs, GGInducesUnitary (p := 2) (f := f) ψ b Y) ∧
      (∃ b ∈ Bs, ∃ (g : GL (Fin 6) K) (t : Kˣ),
        GGInducesUnitary (p := 2) (f := f) ψ b g ∧
          N = g * Matrix.GeneralLinearGroup.scalar (Fin 6) t) ∧
      Module.finrank K
        (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin 6) (Fin 6) K)) 1) = 2 := by
  classical
  obtain ⟨E, hE, _, hE2, hmem, hpre⟩ := ggNSPosLE_exists_E h
  have hx : g₁ ∈ E.comap (QuotientGroup.mk' (Subgroup.center (GL (Fin 6) K))) :=
    hmem b₁ hb₁ g₁ h₁
  have hy : g₂ ∈ E.comap (QuotientGroup.mk' (Subgroup.center (GL (Fin 6) K))) :=
    hmem b₂ hb₂ g₂ h₂
  have hpK : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    have h1 : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ f) 1
    have hd : 2 ^ f + 1 ∣ (2 ^ f) ^ 2 - 1 := by
      rw [h1]
      exact dvd_mul_right _ _
    exact dvd_trans h.dvd hd
  obtain ⟨X, hX, Y, hY, z, hXp, hz, hXY⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.exists_heisenberg_pair
      h.prime h.odd hpK (by norm_num) hE hx hy hne
  obtain ⟨hnm, hEm⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.card_le_of_heisenberg
      h.prime h.odd hpK (by norm_num) hE hX hY hXp hz hXY
  have hdim : Module.finrank K
      (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin 6) (Fin 6) K)) 1) = 2 := by
    have hm2 : 2 ≤ Module.finrank K
        (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin 6) (Fin 6) K)) 1) := by
      have hle := (Nat.pow_le_pow_iff_right h.prime.one_lt).mp (hE2.trans hEm)
      omega
    omega
  obtain ⟨N, hNQ, hNX, hNY, hNns⟩ :=
    ggNSPosPF3C_exists_commutant_nonscalar h.prime h.odd hpK (by norm_num) hE hE2 hX hY
  have hN3 : ∃ s : K, ((N ^ 3 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = s • 1 := by
    obtain ⟨c, hc⟩ := CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.exists_pow_eq_scalar hE hNQ
    refine ⟨(c : K), ?_⟩
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hNns' : ¬ ∃ s : K, (N : Matrix (Fin 6) (Fin 6) K) = s • 1 := by
    rintro ⟨s, hs⟩
    apply hNns
    have hs0 : s ≠ 0 := by
      intro h0
      have h1 : (N : Matrix (Fin 6) (Fin 6) K) *
          ((N⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [hs, h0, zero_smul, zero_mul] at h1
      exact one_ne_zero h1.symm
    refine ⟨Units.mk0 s hs0, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, hs, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  obtain ⟨bX, hbX, gX, hgX, tX, hXt⟩ := hpre X hX
  obtain ⟨bY, hbY, gY, hgY, tY, hYt⟩ := hpre Y hY
  obtain ⟨bN, hbN, gN, hgN, tN, hNt⟩ := hpre N hNQ
  have hYXg : gY * X * gY⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) z * X := by
    rw [hYt] at hXY
    rw [← ggNSPosPF3C_conj_mul_scalar gY X tY]
    exact hXY
  have hNX' : (N : Matrix (Fin 6) (Fin 6) K) * (X : Matrix (Fin 6) (Fin 6) K) =
      (X : Matrix (Fin 6) (Fin 6) K) * (N : Matrix (Fin 6) (Fin 6) K) := by
    simpa only [Units.val_mul] using
      congrArg (fun u : GL (Fin 6) K => (u : Matrix (Fin 6) (Fin 6) K)) hNX
  have hNgY : N * gY = gY * N := by
    rw [hYt] at hNY
    exact ggNSPosPF3C_mul_scalar_comm gY N tY hNY
  have hNY' : (N : Matrix (Fin 6) (Fin 6) K) * (gY : Matrix (Fin 6) (Fin 6) K) =
      (gY : Matrix (Fin 6) (Fin 6) K) * (N : Matrix (Fin 6) (Fin 6) K) := by
    simpa only [Units.val_mul] using
      congrArg (fun u : GL (Fin 6) K => (u : Matrix (Fin 6) (Fin 6) K)) hNgY
  have hYX' : (gY : Matrix (Fin 6) (Fin 6) K) * (X : Matrix (Fin 6) (Fin 6) K) =
      (z : K) • ((X : Matrix (Fin 6) (Fin 6) K) * (gY : Matrix (Fin 6) (Fin 6) K)) := by
    have h1 : gY * X = Matrix.GeneralLinearGroup.scalar (Fin 6) z * (X * gY) := by
      calc gY * X = (gY * X * gY⁻¹) * gY := by group
        _ = (Matrix.GeneralLinearGroup.scalar (Fin 6) z * X) * gY := by rw [hYXg]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 6) z * (X * gY) := by rw [mul_assoc]
    calc (gY : Matrix (Fin 6) (Fin 6) K) * (X : Matrix (Fin 6) (Fin 6) K)
        = ((gY * X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
          rw [Units.val_mul]
      _ = ((Matrix.GeneralLinearGroup.scalar (Fin 6) z * (X * gY) : GL (Fin 6) K) :
            Matrix (Fin 6) (Fin 6) K) := by rw [h1]
      _ = (z : K) • ((X : Matrix (Fin 6) (Fin 6) K) * (gY : Matrix (Fin 6) (Fin 6) K)) := by
          simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
          rw [← Matrix.smul_eq_diagonal_mul]
  exact ⟨(z : K), X, gY, N, hz, hXp, hYX', hNX', hNY', hN3, hNns', ⟨bX, hbX, gX, tX, hgX, hXt⟩,
    ⟨bY, hbY, hgY⟩, ⟨bN, hbN, gN, tN, hgN, hNt⟩, hdim⟩

end CFSG.StandardType

end

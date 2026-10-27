module

public import CFSG.RankThree.PartOne.S11c.SuFiveFixed
public import CFSG.RankThree.PartOne.S11c.SuFivePower
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.S11c.SuFiveAut

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K : Type} [Field K]

theorem isDiag_comm {n : ℕ} {a b : GL (Fin n) K}
    (ha : ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag)
    (hb : ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag) : a * b = b * a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← ha.diagonal_diag, ← hb.diagonal_diag,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  exact mul_comm _ _

theorem exists_pow_five_eq_one_conj (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    {P : unit5 h} {c : Kˣ} (hc : h.norm (c : K) = 1)
    (hP5 : (P : GL (Fin 5) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c)
    {S : Subgroup (GL (Fin 5) K)} (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥)
    (hSP : ∀ s ∈ S, (P : GL (Fin 5) K)⁻¹ * s * (P : GL (Fin 5) K) ∈ S) :
    ∃ P' : unit5 h, (P' : GL (Fin 5) K) ^ 5 = 1 ∧ ∀ g : GL (Fin 5) K,
      (P' : GL (Fin 5) K) * g * (P' : GL (Fin 5) K)⁻¹ =
        (P : GL (Fin 5) K) * g * (P : GL (Fin 5) K)⁻¹ := by
  have hfin : Finite K := h.finite
  have hK2 : 2 ∣ Nat.card K := by
    rw [h.card]
    exact dvd_pow_self 2 (by have := h.one_le; omega)
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_fixSub (by norm_num : 1 ≤ 5) hK2 hS2
  have hW0 : KFSU5.fixSub S ≠ ⊥ := fun hbot => hv0 (by
    have : v ∈ (⊥ : Submodule K (Fin 5 → K)) := hbot ▸ hv
    exact (Submodule.mem_bot K).mp this)
  have hWtop : KFSU5.fixSub S ≠ ⊤ := fun htop => hSne (eq_bot_of_fixSub_eq_top htop)
  obtain ⟨μ, hμ⟩ := exists_fifth_root_of_invariant hP5 hW0 hWtop
    (fun w hw => mulVec_mem_fixSub_of_inv_conj hSP hw)
  have hμn : h.norm (μ : K) = 1 := norm_eq_one_of_norm_pow_five_eq_one h h5 (by
    rw [← Units.val_pow_eq_pow_val, hμ]
    exact hc)
  have hμin : h.norm (((μ⁻¹ : Kˣ)) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hμn, inv_one]
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin 5) μ⁻¹ ∈
      primeFormUnitary h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) :=
    scalar_mem_primeFormUnitary_one h hμin
  refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 5) μ⁻¹ * (P : GL (Fin 5) K),
    mul_mem hsc P.2⟩, ?_, fun g => ?_⟩
  · change (Matrix.GeneralLinearGroup.scalar (Fin 5) μ⁻¹ * (P : GL (Fin 5) K)) ^ 5 = 1
    rw [((commute_scalar μ⁻¹ (P : GL (Fin 5) K)).symm).mul_pow, hP5, ← map_pow, ← map_mul,
      inv_pow, hμ, inv_mul_cancel, map_one]
  · change (Matrix.GeneralLinearGroup.scalar (Fin 5) μ⁻¹ * (P : GL (Fin 5) K)) * g *
      (Matrix.GeneralLinearGroup.scalar (Fin 5) μ⁻¹ * (P : GL (Fin 5) K))⁻¹ = _
    rw [_root_.mul_inv_rev]
    calc Matrix.GeneralLinearGroup.scalar (Fin 5) μ⁻¹ * (P : GL (Fin 5) K) * g *
          ((P : GL (Fin 5) K)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 5) μ⁻¹)⁻¹) =
        Matrix.GeneralLinearGroup.scalar (Fin 5) μ⁻¹ * ((P : GL (Fin 5) K) * g *
          (P : GL (Fin 5) K)⁻¹) * (Matrix.GeneralLinearGroup.scalar (Fin 5) μ⁻¹)⁻¹ := by group
      _ = _ := by
        rw [(commute_scalar μ⁻¹ ((P : GL (Fin 5) K) * g * (P : GL (Fin 5) K)⁻¹)).symm.eq,
          mul_inv_cancel_right]

end CFSG.RankThree.PartOne

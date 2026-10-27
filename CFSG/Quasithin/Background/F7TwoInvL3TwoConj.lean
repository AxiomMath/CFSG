module

public import CFSG.Quasithin.Background.F7TwoInvL3TwoInner
public import CFSG.Quasithin.Background.F7TwoInvL3TwoLin
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] [Finite K]

theorem exists_conjAut_eq_sl3InnerT (hK : ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f) {A : GL (Fin 3) K}
    (hA2 : conjAut 3 K A * conjAut 3 K A = 1) (hA1 : conjAut 3 K A ≠ 1) :
    ∃ H : GL (Fin 3) K, conjAut 3 K A = conjAut 3 K H * sl3InnerT K * (conjAut 3 K H)⁻¹ := by
  have : CharP K 2 := charP_two_of_exists_two_pow_card hK
  have hsq : conjAut 3 K (A * A) * fieldAut 3 K 1 = 1 := by
    rw [map_mul, map_one, mul_one]
    exact hA2
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) (A * A) 1 hsq
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (c : K)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact c.ne_zero (by rw [hr, mul_zero])
  set μ : Kˣ := Units.mk0 r hr0 with hμ
  have hcμ : c = μ * μ := Units.ext (by rw [Units.val_mul, hμ, Units.val_mk0, hr])
  set s : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) μ⁻¹ with hs
  set A' : GL (Fin 3) K := s * A with hA'
  have hA'2 : A' * A' = 1 := by
    have h1 : A * s = s * A := (GeneralLinearGroup.scalar_commute _ _).symm
    calc A' * A' = s * (A * s) * A := by rw [hA']; group
      _ = s * s * (A * A) := by rw [h1]; group
      _ = 1 := by
          rw [← hc, hs, ← map_mul, ← map_mul, hcμ, show μ⁻¹ * μ⁻¹ * (μ * μ) = 1 by group,
            map_one]
  have hcA' : conjAut 3 K A' = conjAut 3 K A := by
    rw [hA', hs, map_mul, conjAut_scalar, one_mul]
  have hmat2 : (A' : Matrix (Fin 3) (Fin 3) K) * (A' : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, hA'2, Units.val_one]
  have hmat1 : (A' : Matrix (Fin 3) (Fin 3) K) ≠ 1 := by
    intro h
    apply hA1
    rw [← hcA', Units.ext (h.trans Units.val_one.symm), map_one]
  obtain ⟨Hm, hHu, hH⟩ := exists_isUnit_mul_eq_transvection hmat2 hmat1
  have hAH : A' = hHu.unit * SpecialLinearGroup.toGL (sl3ElemE K) * hHu.unit⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, IsUnit.unit_spec]
    exact hH
  refine ⟨hHu.unit, ?_⟩
  calc conjAut 3 K A = conjAut 3 K A' := hcA'.symm
    _ = conjAut 3 K (hHu.unit * SpecialLinearGroup.toGL (sl3ElemE K) * hHu.unit⁻¹) := by rw [← hAH]
    _ = conjAut 3 K hHu.unit * sl3InnerT K * (conjAut 3 K hHu.unit)⁻¹ := by
      simp only [map_mul, map_inv]
      rfl

theorem invAutGen_conjAut (hK : ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f) {A : GL (Fin 3) K}
    (hA2 : conjAut 3 K A * conjAut 3 K A = 1) (hA1 : conjAut 3 K A ≠ 1) :
    InvAutGen (projectiveSL 3 K) (conjAut 3 K A) := by
  obtain ⟨H, hH⟩ := exists_conjAut_eq_sl3InnerT hK hA2 hA1
  rw [hH]
  exact (InvAutGen.conj_iff _ _).1 (invAutGen_sl3InnerT hK)

end CFSG.Quasithin.F7Two

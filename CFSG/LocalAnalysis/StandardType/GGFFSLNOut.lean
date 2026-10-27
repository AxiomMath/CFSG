module

public import CFSG.LocalAnalysis.StandardType.GGFFModelNDefs
public import CFSG.LocalAnalysis.StandardType.GGFFSLNDefs
import CFSG.RankThree.PartOne.TAIL.LSideOutAut
import CFSG.Assembly.QuasithinDefs
import CFSG.CharacterTheory.Semidihedral.SemilinearOuterQuotient
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartOne.TAIL.KSideCen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF

open scoped MatrixGroups

open CFSG.RankThree.PartTwo.Sec4.RonanK429F
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut slGraphAut_matrix)

private theorem conj_pow {R : Type*} [Monoid R] {K A Ki : R}
    (hK : K * Ki = 1) (hKi : Ki * K = 1) (n : ℕ) :
    (K * A * Ki) ^ n = K * A ^ n * Ki := by
  induction n with
  | zero => simp [hK]
  | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      calc K * A ^ n * Ki * (K * A * Ki) = K * A ^ n * (Ki * K) * A * Ki := by
            noncomm_ring
        _ = K * A ^ n * A * Ki := by rw [hKi]; noncomm_ring
        _ = K * (A ^ n * A) * Ki := by noncomm_ring

private theorem conj_cubic {R : Type*} [Ring R] {K A Ki : R}
    (hK : K * Ki = 1) (hKi : Ki * K = 1) :
    (K * A * Ki) ^ 3 + K * A * Ki + 1 = K * (A ^ 3 + A + 1) * Ki := by
  rw [conj_pow hK hKi 3]
  calc K * A ^ 3 * Ki + K * A * Ki + 1 =
        K * A ^ 3 * Ki + K * A * Ki + K * Ki := by
        rw [show (1 : R) = K * Ki from hK.symm]
    _ = K * (A ^ 3 + A + 1) * Ki := by noncomm_ring

private theorem conj_quartic {R : Type*} [Ring R] {K A Ki : R}
    (hK : K * Ki = 1) (hKi : Ki * K = 1) :
    (K * A * Ki) ^ 4 + (K * A * Ki) ^ 3 + (K * A * Ki) ^ 2 + 1 =
      K * (A ^ 4 + A ^ 3 + A ^ 2 + 1) * Ki := by
  rw [conj_pow hK hKi 4, conj_pow hK hKi 3, conj_pow hK hKi 2]
  calc K * A ^ 4 * Ki + K * A ^ 3 * Ki + K * A ^ 2 * Ki + 1 =
        K * A ^ 4 * Ki + K * A ^ 3 * Ki + K * A ^ 2 * Ki + K * Ki := by
        rw [show (1 : R) = K * Ki from hK.symm]
    _ = K * (A ^ 4 + A ^ 3 + A ^ 2 + 1) * Ki := by noncomm_ring

private theorem eq_zero_of_conj_eq_zero {R : Type*} [Ring R] {K B Ki : R}
    (hKi : Ki * K = 1) (h : K * B * Ki = 0) : B = 0 := by
  have h1 : B = (1 : R) * B * 1 := by noncomm_ring
  rw [h1, ← hKi]
  calc (Ki * K) * B * (Ki * K) = Ki * (K * B * Ki) * K := by noncomm_ring
    _ = Ki * 0 * K := by rw [h]
    _ = 0 := by noncomm_ring

private theorem g6_pow_seven : gOf N6.r N6.r' ^ 7 = 1 := by decide +kernel

private theorem g7_pow_seven : gOf N7.r N7.r' ^ 7 = 1 := by decide +kernel

private theorem pow_six_eq_inv {G : Type*} [Group G] {x : G} (h : x ^ 7 = 1) :
    x ^ 6 = x⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_succ]
  simpa using h

private theorem g6_poly_pow (j : ℕ)
    (hj : j % 7 = 1 ∨ j % 7 = 2 ∨ j % 7 = 4) :
    (((gOf N6.r N6.r') ^ j : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 3 +
      (((gOf N6.r N6.r') ^ j : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) + 1 = 0 := by
  rw [pow_eq_pow_mod j g6_pow_seven]
  rcases hj with h | h | h <;> rw [h] <;> decide +kernel

private theorem g6_poly_six_ne_zero :
    ((((gOf N6.r N6.r') ^ 6 : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 3 +
      (((gOf N6.r N6.r') ^ 6 : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) + 1) ≠ 0 := by
  decide +kernel

private theorem g7_quartic_pow (j : ℕ)
    (hj : j % 7 = 1 ∨ j % 7 = 2 ∨ j % 7 = 4) :
    (((gOf N7.r N7.r') ^ j : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 4 +
      (((gOf N7.r N7.r') ^ j : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 3 +
      (((gOf N7.r N7.r') ^ j : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 2 + 1 = 0 := by
  rw [pow_eq_pow_mod j g7_pow_seven]
  rcases hj with h | h | h <;> rw [h] <;> decide +kernel

private theorem g7_quartic_six_ne_zero :
    ((((gOf N7.r N7.r') ^ 6 : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 4 +
      (((gOf N7.r N7.r') ^ 6 : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 3 +
      (((gOf N7.r N7.r') ^ 6 : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 2 + 1) ≠ 0 := by
  decide +kernel

theorem out_SL {n : ℕ} (hn : 3 ≤ n) : ∀ α β : MulAut SL(n, ZMod 2),
    (∃ k, α = MulAut.conj k) ∨ (∃ k, β = MulAut.conj k) ∨ ∃ k, α * β = MulAut.conj k := by
  intro α β
  obtain ⟨a, ε, hε, hα⟩ := CFSG.RankThree.PartOne.TAIL.aut_sl_zmod_two hn α
  obtain ⟨b, η, hη, hβ⟩ := CFSG.RankThree.PartOne.TAIL.aut_sl_zmod_two hn β
  by_cases hε0 : ε = 0
  · left
    exact ⟨a, by rw [hα, hε0, pow_zero, mul_one]⟩
  by_cases hη0 : η = 0
  · right; left
    exact ⟨b, by rw [hβ, hη0, pow_zero, mul_one]⟩
  right; right
  have hε1 : ε = 1 := by omega
  have hη1 : η = 1 := by omega
  refine ⟨a * slGraphAut n (ZMod 2) b, ?_⟩
  rw [hα, hβ, hε1, hη1]
  have hcomm : slGraphAut n (ZMod 2) * MulAut.conj b =
      MulAut.conj (slGraphAut n (ZMod 2) b) * slGraphAut n (ZMod 2) := by
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  have hδ2 : slGraphAut n (ZMod 2) * slGraphAut n (ZMod 2) = 1 := by
    rw [← pow_two]
    exact CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_sq n (ZMod 2)
  calc MulAut.conj a * slGraphAut n (ZMod 2) * (MulAut.conj b * slGraphAut n (ZMod 2))
      = MulAut.conj a * (slGraphAut n (ZMod 2) * MulAut.conj b) *
          slGraphAut n (ZMod 2) := by simp only [mul_assoc]
    _ = MulAut.conj a * (MulAut.conj (slGraphAut n (ZMod 2) b) *
          slGraphAut n (ZMod 2)) * slGraphAut n (ZMod 2) := by rw [hcomm]
    _ = MulAut.conj a * MulAut.conj (slGraphAut n (ZMod 2) b) *
          (slGraphAut n (ZMod 2) * slGraphAut n (ZMod 2)) := by simp only [mul_assoc]
    _ = MulAut.conj a * MulAut.conj (slGraphAut n (ZMod 2) b) := by rw [hδ2, mul_one]
    _ = MulAut.conj (a * slGraphAut n (ZMod 2) b) := by rw [map_mul]

theorem g_out_SL6 : ∀ α : MulAut SL(6, ZMod 2), (∀ k : SL(6, ZMod 2), α ≠ MulAut.conj k) →
    ∀ (k : SL(6, ZMod 2)) (j : ℕ), (j % 7 = 1 ∨ j % 7 = 2 ∨ j % 7 = 4) →
      α (gOf N6.r N6.r') ≠ k * gOf N6.r N6.r' ^ j * k⁻¹ := by
  intro α hout k j hj h
  set g : SL(6, ZMod 2) := gOf N6.r N6.r' with hg
  obtain ⟨c, ε, hε, hα⟩ :=
    CFSG.RankThree.PartOne.TAIL.aut_sl_zmod_two (n := 6) (by norm_num) α
  have hε0 : ε ≠ 0 := by
    intro h0
    exact hout c (by rw [hα, h0, pow_zero, mul_one])
  have hε1 : ε = 1 := by omega
  set δ : MulAut (SL(6, ZMod 2)) := slGraphAut 6 (ZMod 2) with hδ
  have hαg : α g = c * δ g * c⁻¹ := by
    rw [hα, hε1, pow_one, hδ]
    rfl
  have hHK : c * δ g * c⁻¹ = k * g ^ j * k⁻¹ := by
    rw [← hαg]
    exact h
  set K : SL(6, ZMod 2) := k⁻¹ * c with hK
  have hconj : g ^ j = K * δ g * K⁻¹ := by
    calc g ^ j = k⁻¹ * (k * g ^ j * k⁻¹) * k := by group
      _ = k⁻¹ * (c * δ g * c⁻¹) * k := by rw [← hHK]
      _ = K * δ g * K⁻¹ := by rw [hK]; group
  have hδm : ((g ^ j : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      (K : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
        ((δ g : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
        ((K⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    rw [hconj]
    simp only [Matrix.SpecialLinearGroup.coe_mul]
  have hKKi : (K : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      ((K⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hKiK : ((K⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      (K : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hpolyj : ((g ^ j : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 3 +
      ((g ^ j : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) + 1 = 0 := by
    rw [hg]
    exact g6_poly_pow j hj
  have hphpoly : (K : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      (((δ g : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 3 +
        ((δ g : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) + 1) *
      ((K⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 0 := by
    rw [← conj_cubic hKKi hKiK]
    simpa [hδm] using hpolyj
  have hAzero : (((δ g : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 3 +
      ((δ g : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) + 1) = 0 :=
    eq_zero_of_conj_eq_zero hKiK hphpoly
  have hB : ((g⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 3 +
      ((g⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) + 1 = 0 := by
    have htr := congrArg Matrix.transpose hAzero
    rw [hδ, slGraphAut_matrix] at htr
    simpa [Matrix.transpose_pow] using htr
  have hginv : g ^ 6 = g⁻¹ := pow_six_eq_inv (by rw [hg]; exact g6_pow_seven)
  have hB6 : (((g ^ 6 : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 3 +
      ((g ^ 6 : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) + 1) = 0 := by
    rw [hginv]
    exact hB
  have hne : (((g ^ 6 : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 3 +
      ((g ^ 6 : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) + 1) ≠ 0 := by
    rw [hg]
    exact g6_poly_six_ne_zero
  exact hne hB6

theorem g_out_SL7 : ∀ α : MulAut SL(7, ZMod 2), (∀ k : SL(7, ZMod 2), α ≠ MulAut.conj k) →
    ∀ (k : SL(7, ZMod 2)) (j : ℕ), (j % 7 = 1 ∨ j % 7 = 2 ∨ j % 7 = 4) →
      α (gOf N7.r N7.r') ≠ k * gOf N7.r N7.r' ^ j * k⁻¹ := by
  intro α hout k j hj h
  set g : SL(7, ZMod 2) := gOf N7.r N7.r' with hg
  obtain ⟨c, ε, hε, hα⟩ :=
    CFSG.RankThree.PartOne.TAIL.aut_sl_zmod_two (n := 7) (by norm_num) α
  have hε0 : ε ≠ 0 := by
    intro h0
    exact hout c (by rw [hα, h0, pow_zero, mul_one])
  have hε1 : ε = 1 := by omega
  set δ : MulAut (SL(7, ZMod 2)) := slGraphAut 7 (ZMod 2) with hδ
  have hαg : α g = c * δ g * c⁻¹ := by
    rw [hα, hε1, pow_one, hδ]
    rfl
  have hHK : c * δ g * c⁻¹ = k * g ^ j * k⁻¹ := by
    rw [← hαg]
    exact h
  set K : SL(7, ZMod 2) := k⁻¹ * c with hK
  have hconj : g ^ j = K * δ g * K⁻¹ := by
    calc g ^ j = k⁻¹ * (k * g ^ j * k⁻¹) * k := by group
      _ = k⁻¹ * (c * δ g * c⁻¹) * k := by rw [← hHK]
      _ = K * δ g * K⁻¹ := by rw [hK]; group
  have hδm : ((g ^ j : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
      (K : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
        ((δ g : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
        ((K⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
    rw [hconj]
    simp only [Matrix.SpecialLinearGroup.coe_mul]
  have hKKi : (K : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
      ((K⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hKiK : ((K⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
      (K : Matrix (Fin 7) (Fin 7) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hpolyj : ((g ^ j : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 4 +
      ((g ^ j : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 3 +
      ((g ^ j : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 2 + 1 = 0 := by
    rw [hg]
    exact g7_quartic_pow j hj
  have hphpoly : (K : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
      (((δ g : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 4 +
        ((δ g : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 3 +
        ((δ g : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 2 + 1) *
      ((K⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) = 0 := by
    rw [← conj_quartic hKKi hKiK]
    simpa [hδm] using hpolyj
  have hAzero : (((δ g : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 4 +
      ((δ g : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 3 +
      ((δ g : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 2 + 1) = 0 :=
    eq_zero_of_conj_eq_zero hKiK hphpoly
  have hB : ((g⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 4 +
      ((g⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 3 +
      ((g⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 2 + 1 = 0 := by
    have htr := congrArg Matrix.transpose hAzero
    rw [hδ, slGraphAut_matrix] at htr
    simpa [Matrix.transpose_pow] using htr
  have hginv : g ^ 6 = g⁻¹ := pow_six_eq_inv (by rw [hg]; exact g7_pow_seven)
  have hB6 : (((g ^ 6 : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 4 +
      ((g ^ 6 : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 3 +
      ((g ^ 6 : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 2 + 1) = 0 := by
    rw [hginv]
    exact hB
  have hne : (((g ^ 6 : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 4 +
      ((g ^ 6 : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 3 +
      ((g ^ 6 : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 2 + 1) ≠ 0 := by
    rw [hg]
    exact g7_quartic_six_ne_zero
  exact hne hB6

end CFSG.StandardType.GGFF

end

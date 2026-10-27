module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFL34Uni
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree

public section

namespace CFSG.Quasithin.SBd19F

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

variable {k : Type} [Field k]

theorem mem_linearAutGroup_of_pow_three (hk : Nat.card k = 4) {α : MulAut (projectiveSL 3 k)}
    (hα : α ^ 3 = 1) : α ∈ linearAutGroup 3 k := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  by_contra hD
  obtain ⟨σ, hσ, -⟩ :=
    CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent le_rfl α hα hD
  let σ₀ : k ≃+* k := frobeniusEquiv k 2
  have hσ₀ : ∀ a, σ₀ a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  have h2 : σ * σ = 1 := by
    rcases LinearThreeFourOuter.ringEquiv_eq_one_or hσ₀ hk σ with h | h
    · rw [h]
      rfl
    · rw [h]
      exact LinearThreeFourOuter.sigma_mul_self hσ₀ hk
  have hdvd : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
  rw [hσ] at hdvd
  omega

theorem comm_of_conjAut_fixes [CharP k 2] {B : GL (Fin 3) k} {A : SpecialLinearGroup (Fin 3) k}
    (hA : A ∈ unitriangular 3 k) (h : conjAut 3 k B (proj 3 k A) = proj 3 k A) :
    (B : Matrix (Fin 3) (Fin 3) k) * (A : Matrix (Fin 3) (Fin 3) k) =
      (A : Matrix (Fin 3) (Fin 3) k) * (B : Matrix (Fin 3) (Fin 3) k) := by
  rw [conjAut_proj, proj_eq_proj_iff] at h
  obtain ⟨c, -, hc⟩ := mem_scalars.mp h
  set S := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k B A
    with hSdef
  have hmul : ((S * (S⁻¹ * A) : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      (S : Matrix (Fin 3) (Fin 3) k) *
        ((S⁻¹ * A : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) :=
    Matrix.SpecialLinearGroup.coe_mul _ _
  have hA' : (A : Matrix (Fin 3) (Fin 3) k) =
      (S : Matrix (Fin 3) (Fin 3) k) * Matrix.scalar (Fin 3) (c : k) :=
    calc (A : Matrix (Fin 3) (Fin 3) k)
        = ((S * (S⁻¹ * A) : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
          rw [mul_inv_cancel_left]
      _ = (S : Matrix (Fin 3) (Fin 3) k) * Matrix.scalar (Fin 3) (c : k) := by rw [hmul, hc]
  rw [hSdef, coe_slConjugation, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    Matrix.mul_smul, mul_one] at hA'
  have htr := congrArg Matrix.trace hA'
  have hcyc : Matrix.trace ((B : Matrix (Fin 3) (Fin 3) k) * (A : Matrix (Fin 3) (Fin 3) k) *
      ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) =
      Matrix.trace (A : Matrix (Fin 3) (Fin 3) k) := by
    rw [Matrix.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
  rw [Matrix.trace_smul, hcyc] at htr
  obtain ⟨-, hdiag⟩ := hA
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have htrA : Matrix.trace (A : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [Matrix.trace_fin_three, hdiag 0, hdiag 1, hdiag 2]
    linear_combination h2
  rw [htrA] at htr
  have hc1 : (c : k) = 1 := by simpa using htr.symm
  rw [hc1, one_smul] at hA'
  calc (B : Matrix (Fin 3) (Fin 3) k) * (A : Matrix (Fin 3) (Fin 3) k)
      = ((B : Matrix (Fin 3) (Fin 3) k) * (A : Matrix (Fin 3) (Fin 3) k) *
        ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) * (B : Matrix (Fin 3) (Fin 3) k) := by
        rw [mul_assoc ((B : Matrix (Fin 3) (Fin 3) k) * (A : Matrix (Fin 3) (Fin 3) k)),
          Units.inv_mul, mul_one]
    _ = (A : Matrix (Fin 3) (Fin 3) k) * (B : Matrix (Fin 3) (Fin 3) k) := by rw [← hA']

theorem eq_scalar_of_comm [CharP k 2] {C A : Matrix (Fin 3) (Fin 3) k}
    (h10 : A 1 0 = 0) (h21 : A 2 1 = 0)
    (h00 : A 0 0 = 1) (h11 : A 1 1 = 1) (h22 : A 2 2 = 1)
    (hnz : ¬ (A 0 1 = 0 ∧ A 1 2 = 0))
    (hW : C * wM 1 = wM 1 * C) (hAC : C * A = A * C)
    (u₀ : k) (hu₀ : u₀ ≠ 0) (hC3 : C * C * C = Matrix.scalar (Fin 3) u₀) :
    ∃ a : k, a ≠ 0 ∧ C = Matrix.scalar (Fin 3) a := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have e12 := congrFun (congrFun hW 1) 2
  have e22 := congrFun (congrFun hW 2) 2
  have e01 := congrFun (congrFun hW 0) 1
  have e02 := congrFun (congrFun hW 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, wM] at e12 e22 e01 e02
  have c00 : C 0 0 = C 2 2 := by linear_combination e02
  have f01 := congrFun (congrFun hAC 0) 1
  have f12 := congrFun (congrFun hAC 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h21, h00, h11, h22, e12, e01] at f01 f12
  have hα : A 0 1 * (C 0 0 - C 1 1) = 0 := by linear_combination f01
  have hγ : A 1 2 * (C 1 1 - C 0 0) = 0 := by linear_combination f12 - A 1 2 * c00
  have hm : C 1 1 = C 0 0 := by
    by_cases h : A 0 1 = 0
    · have hg : A 1 2 ≠ 0 := fun h' => hnz ⟨h, h'⟩
      have := (mul_eq_zero.mp hγ).resolve_left hg
      linear_combination this
    · have := (mul_eq_zero.mp hα).resolve_left h
      linear_combination -this
  have g00 := congrFun (congrFun hC3 0) 0
  have g01 := congrFun (congrFun hC3 0) 1
  have g12 := congrFun (congrFun hC3 1) 2
  have g02 := congrFun (congrFun hC3 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, e12, e22, e01] at g00 g01 g12 g02
  have ha : C 0 0 ≠ 0 := fun h => hu₀ (by rw [← g00, h]; ring)
  have c22 : C 2 2 = C 0 0 := c00.symm
  rw [hm] at g01 g12
  rw [c22] at g12 g02
  rw [hm] at g02
  have hp : C 0 1 = 0 := by
    have : C 0 0 ^ 2 * C 0 1 = 0 := by linear_combination g01 - (C 0 0 ^ 2 * C 0 1) * h2
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 ha)
  have hn : C 1 2 = 0 := by
    have : C 0 0 ^ 2 * C 1 2 = 0 := by linear_combination g12 - (C 0 0 ^ 2 * C 1 2) * h2
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 ha)
  have hq : C 0 2 = 0 := by
    rw [hp, hn] at g02
    have : C 0 0 ^ 2 * C 0 2 = 0 := by linear_combination g02 - (C 0 0 ^ 2 * C 0 2) * h2
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 ha)
  refine ⟨C 0 0, ha, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hm, c22, hp, hn, hq, e12, e22, e01]

theorem eq_one_of_fixes (hk : Nat.card k = 4) {α : MulAut (projectiveSL 3 k)} (hα3 : α ^ 3 = 1)
    (hw : α (wP 1) = wP 1) {A : SpecialLinearGroup (Fin 3) k} (hA : A ∈ unitriangular 3 k)
    (hnz : ¬ ((A : Matrix (Fin 3) (Fin 3) k) 0 1 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) k) 1 2 = 0))
    (hfix : α (proj 3 k A) = proj 3 k A) : α = 1 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  obtain ⟨B, hB⟩ : α ∈ (conjAut 3 k).range := by
    rw [← linearAutGroup_eq_range]
    exact mem_linearAutGroup_of_pow_three hk hα3
  have hwm := comm_of_conjAut_fixes (B := B) (wMat_mem_unitriangular 1) (by rw [hB]; exact hw)
  have hAm := comm_of_conjAut_fixes (B := B) hA (by rw [hB]; exact hfix)
  have hB3 : ∃ u : kˣ, B ^ 3 = GeneralLinearGroup.scalar (Fin 3) u := by
    have : conjAut 3 k (B ^ 3) = 1 := by rw [map_pow, hB, hα3]
    exact (ProjectivePlane.conjAut_eq_one_iff (by norm_num) _).mp this
  obtain ⟨u, hu⟩ := hB3
  have hC3 : (B : Matrix (Fin 3) (Fin 3) k) * B * B = Matrix.scalar (Fin 3) (u : k) := by
    have := congrArg (fun g : GL (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k)) hu
    simpa [pow_succ] using this
  obtain ⟨hlow, hdiag⟩ := hA
  obtain ⟨a, ha, hC⟩ := eq_scalar_of_comm (hlow 1 0 (by decide)) (hlow 2 1 (by decide))
    (hdiag 0) (hdiag 1) (hdiag 2) hnz hwm hAm (u : k) u.ne_zero hC3
  have hBs : B = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 a ha) := by
    apply Units.ext
    simpa using hC
  rw [← hB, hBs]
  exact conjAut_scalar _

end CFSG.Quasithin.SBd19F

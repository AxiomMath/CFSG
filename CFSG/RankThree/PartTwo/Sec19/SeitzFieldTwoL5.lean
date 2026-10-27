module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSLRoot

public section

namespace CFSG.RankThree.PartTwo.Sec19

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.CTP
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

theorem linearAutGroup_eq_range_conjAut (n : ℕ) (K : Type) [Field K] :
    linearAutGroup n K = (conjAut n K).range := by
  rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]

theorem scalar_three_eq_smul_one {F : Type} [Field F] (c : F) :
    scalar (Fin 3) c = c • (1 : Matrix (Fin 3) (Fin 3) F) := by
  rw [scalar_apply, smul_one_eq_diagonal]

theorem trace_one_add_single {F : Type} [Field F] {i j : Fin 3} (hij : i ≠ j) :
    trace ((1 : Matrix (Fin 3) (Fin 3) F) + single i j 1) = 3 := by
  simp [trace_add, trace_one, trace_single_eq_of_ne, hij]

theorem exists_scalar_of_proj_eq {F : Type} [Field F] (Y : GL (Fin 3) F)
    (g : SpecialLinearGroup (Fin 3) F) (h : proj 3 F (slConjugation 3 F Y g) = proj 3 F g) :
    ∃ c : F, (Y : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) *
        ((Y⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * scalar (Fin 3) c := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_proj_iff.mp h.symm)
  refine ⟨(c : F), ?_⟩
  have e : ((slConjugation 3 F Y g : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) *
      ((g⁻¹ * slConjugation 3 F Y g : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) := by
    conv_lhs => rw [(mul_inv_cancel_left g (slConjugation 3 F Y g)).symm]
    rfl
  rw [hc, coe_slConjugation] at e
  exact e

theorem eq_one_of_conj_scalar {F : Type} [Field F] (h3 : (3 : F) ≠ 0)
    {X X' G : Matrix (Fin 3) (Fin 3) F} {c : F} (hX'X : X' * X = 1)
    (hG : trace G = 3) (hc : X * G * X' = G * scalar (Fin 3) c) : c = 1 := by
  have ht := congrArg trace hc
  rw [trace_mul_comm (X * G) X', ← mul_assoc, hX'X, one_mul, scalar_three_eq_smul_one,
    Matrix.mul_smul, mul_one, trace_smul, smul_eq_mul, hG] at ht
  exact mul_right_cancel₀ h3 (by rw [one_mul]; exact ht.symm)

theorem trace_conj_eq {F : Type} [Field F] {H H' M : Matrix (Fin 3) (Fin 3) F}
    (hHH : H' * H = 1) : trace (H * M * H') = trace M := by
  rw [trace_mul_comm, ← mul_assoc, hHH, one_mul]

theorem mul_eq_mul_of_conj_eq {F : Type} [Field F] {X X' G : Matrix (Fin 3) (Fin 3) F}
    (hX'X : X' * X = 1) (hc : X * G * X' = G) : X * G = G * X := by
  calc X * G = X * G * (X' * X) := by rw [hX'X, mul_one]
    _ = X * G * X' * X := by rw [mul_assoc (X * G) X' X]
    _ = G * X := by rw [hc]

theorem b5_conj_cancel {α : Type*} [Monoid α] {P Q Z : α} (hPQ : P * Q = 1) :
    P * (Q * Z * P) * Q = Z := by
  calc P * (Q * Z * P) * Q = (P * Q) * Z * (P * Q) := by simp only [mul_assoc]
    _ = Z := by rw [hPQ, one_mul, mul_one]

theorem b5_commute_of_conj {α : Type*} [Monoid α] {P Q Yn M : α} (hQP : Q * P = 1)
    (h : Yn * (P * M * Q) = P * M * Q * Yn) : (Q * Yn * P) * M = M * (Q * Yn * P) := by
  calc (Q * Yn * P) * M = (Q * Yn * P) * M * (Q * P) := by rw [hQP, mul_one]
    _ = Q * (Yn * (P * M * Q)) * P := by simp only [mul_assoc]
    _ = Q * (P * M * Q * Yn) * P := by rw [h]
    _ = (Q * P) * (M * (Q * Yn * P)) := by simp only [mul_assoc]
    _ = M * (Q * Yn * P) := by rw [hQP, one_mul]

theorem b5_commute_of_one_add {α : Type*} [Ring α] {W E : α}
    (h : W * (1 + E) = (1 + E) * W) : W * E = E * W := by
  have h' : W + W * E = W + E * W := by
    rw [mul_add, add_mul, mul_one, one_mul] at h
    exact h
  exact add_left_cancel h'

theorem b5_conj_transvection {F : Type} [Field F] (h3 : (3 : F) ≠ 0) {k : Subfield F}
    {H Y : GL (Fin 3) F}
    (hfix : ∀ S ∈ slSub 3 k,
      conjAut 3 F Y (proj 3 F (slConjugation 3 F H S)) = proj 3 F (slConjugation 3 F H S))
    {i j : Fin 3} (hij : i ≠ j) :
    (Y : Matrix (Fin 3) (Fin 3) F) * ((H : Matrix (Fin 3) (Fin 3) F) *
        (1 + single i j (1 : F)) * ((H⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =
      ((H : Matrix (Fin 3) (Fin 3) F) * (1 + single i j (1 : F)) *
        ((H⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) * (Y : Matrix (Fin 3) (Fin 3) F) := by
  have h := hfix _ (transvection_mem_slSub hij k.one_mem)
  rw [conjAut_proj] at h
  obtain ⟨c, hc⟩ := exists_scalar_of_proj_eq Y _ h
  have htr : trace ((slConjugation 3 F H (SpecialLinearGroup.transvection hij 1) :
      SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 3 := by
    rw [coe_slConjugation, trace_conj_eq (Units.inv_mul H), SpecialLinearGroup.transvection_coe]
    exact trace_one_add_single hij
  have hc1 : c = 1 := eq_one_of_conj_scalar h3 (Units.inv_mul Y) htr hc
  rw [hc1, map_one, mul_one, coe_slConjugation, SpecialLinearGroup.transvection_coe] at hc
  exact mul_eq_mul_of_conj_eq (Units.inv_mul Y) hc

theorem b5_commute_single {F : Type} [Field F] {H Y : GL (Fin 3) F} {i j : Fin 3}
    (hc : (Y : Matrix (Fin 3) (Fin 3) F) * ((H : Matrix (Fin 3) (Fin 3) F) *
        (1 + single i j (1 : F)) * ((H⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =
      ((H : Matrix (Fin 3) (Fin 3) F) * (1 + single i j (1 : F)) *
        ((H⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) * (Y : Matrix (Fin 3) (Fin 3) F)) :
    (((H⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (Y : Matrix (Fin 3) (Fin 3) F) *
        (H : Matrix (Fin 3) (Fin 3) F)) * single i j (1 : F) =
      single i j (1 : F) * (((H⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (Y : Matrix (Fin 3) (Fin 3) F) * (H : Matrix (Fin 3) (Fin 3) F)) :=
  b5_commute_of_one_add (b5_commute_of_conj (Units.inv_mul H) hc)

theorem eq_one_of_fixes_conj_slSub {F : Type} [Field F] [Finite F] (h3 : (3 : F) ≠ 0)
    {k : Subfield F} {H : GL (Fin 3) F} {y : MulAut (projectiveSL 3 F)}
    (hy : y ∈ linearAutGroup 3 F)
    (hfix : ∀ S ∈ slSub 3 k,
      y (proj 3 F (slConjugation 3 F H S)) = proj 3 F (slConjugation 3 F H S)) :
    y = 1 := by
  rw [linearAutGroup_eq_range_conjAut] at hy
  obtain ⟨Y, rfl⟩ := MonoidHom.mem_range.mp hy
  obtain ⟨c, hc⟩ : ∃ c : F, scalar (Fin 3) c =
      ((H⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (Y : Matrix (Fin 3) (Fin 3) F) *
        (H : Matrix (Fin 3) (Fin 3) F) := by
    apply mem_range_scalar_of_commute_single
    intro i j hij
    exact (b5_commute_single (b5_conj_transvection h3 hfix hij)).symm
  have hYW : (H : Matrix (Fin 3) (Fin 3) F) *
      (((H⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (Y : Matrix (Fin 3) (Fin 3) F) *
        (H : Matrix (Fin 3) (Fin 3) F)) *
      ((H⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (Y : Matrix (Fin 3) (Fin 3) F) :=
    b5_conj_cancel (Units.mul_inv H)
  rw [← hc] at hYW
  have hcomm : Commute (scalar (Fin 3) c) (H : Matrix (Fin 3) (Fin 3) F) :=
    Matrix.scalar_commute c (fun r' => Commute.all c r') _
  have hYs : (Y : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) c := by
    rw [← hYW, ← hcomm.eq, mul_assoc, Units.mul_inv, mul_one]
  have hcg : ∀ g : SpecialLinearGroup (Fin 3) F, slConjugation 3 F Y g = g := by
    intro g
    have hm : ((slConjugation 3 F Y g : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) := by
      rw [coe_slConjugation, hYs,
        (Matrix.scalar_commute c (fun r' => Commute.all c r') (g : Matrix (Fin 3) (Fin 3) F)).eq,
        ← hYs, mul_assoc, Units.mul_inv, mul_one]
    exact Matrix.SpecialLinearGroup.ext (slConjugation 3 F Y g) g
      (fun i j => congrFun (congrFun hm i) j)
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  rw [conjAut_proj, hcg g, MulAut.one_apply]

end CFSG.RankThree.PartTwo.Sec19

end

module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKLinStab
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open Matrix

variable {F : Type} [Field F]

private theorem transvection_mulVec_hom {i j : Fin 3} (hij : i ≠ j) (b : F) (v : Fin 3 → F) :
    (Matrix.SpecialLinearGroup.transvection hij b : Matrix (Fin 3) (Fin 3) F).mulVec v =
      v + Pi.single i (b * v j) := by
  rw [Matrix.SpecialLinearGroup.transvection_coe, add_mulVec, one_mulVec, single_mulVec]
  rfl

private theorem exists_sl3_col_zero_hom {v : Fin 3 → F} (hv : v 0 ≠ 0) :
    ∃ k : Matrix.SpecialLinearGroup (Fin 3) F,
      (k : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 0 1 : Fin 3 → F) = v := by
  refine ⟨⟨!![v 0, 0, 0; v 1, 1, 0; v 2, 0, (v 0)⁻¹], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_three]
    simp [hv]
  · funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply]

private theorem exists_sl3_coord_zero_ne_hom {v : Fin 3 → F} (hv : v ≠ 0) :
    ∃ t : Matrix.SpecialLinearGroup (Fin 3) F, ((t : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 ≠ 0 := by
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · have h2 : v 2 ≠ 0 := by
        intro h2
        apply hv
        funext i
        fin_cases i <;> simp [h0, h1, h2]
      refine ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) 1, ?_⟩
      rw [transvection_mulVec_hom]
      simp [h0, h2]
    · refine ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1, ?_⟩
      rw [transvection_mulVec_hom]
      simp [h0, h1]
  · exact ⟨1, by simpa using h0⟩

private theorem exists_sl3_mulVec_eq_single_hom {v : Fin 3 → F} (hv : v ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) F,
      (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = (Pi.single 0 1 : Fin 3 → F) := by
  obtain ⟨t, ht⟩ := exists_sl3_coord_zero_ne_hom hv
  obtain ⟨k, hk⟩ := exists_sl3_col_zero_hom (v := (t : Matrix (Fin 3) (Fin 3) F) *ᵥ v) ht
  have hki : ((k⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (k : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  refine ⟨k⁻¹ * t, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, ← hk, mulVec_mulVec, hki, one_mulVec]

private def lowerBlock_hom (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun i j => A i.succ j.succ

private theorem lowerBlock_mul_hom {A B : Matrix (Fin 3) (Fin 3) F}
    (hA1 : A 1 0 = 0) (hA2 : A 2 0 = 0) :
    lowerBlock_hom (A * B) = lowerBlock_hom A * lowerBlock_hom B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerBlock_hom, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hA1, hA2]

private theorem det_lowerBlock_hom {A : Matrix (Fin 3) (Fin 3) F}
    (h00 : A 0 0 = 1) (h10 : A 1 0 = 0) (h20 : A 2 0 = 0) :
    (lowerBlock_hom A).det = A.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_three]
  simp [lowerBlock_hom, h00, h10, h20]

private theorem col_zero_hom {A : Matrix (Fin 3) (Fin 3) F}
    (h : A *ᵥ (Pi.single 0 1 : Fin 3 → F) = Pi.single 0 1) :
    A 0 0 = 1 ∧ A 1 0 = 0 ∧ A 2 0 = 0 := by
  have hc0 := congrFun h 0
  have hc1 := congrFun h 1
  have hc2 := congrFun h 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply] at hc0 hc1 hc2
  exact ⟨hc0, hc1, hc2⟩

private theorem mul_self_eq_one_of_lowerBlock_hom {A : Matrix (Fin 3) (Fin 3) F}
    (h2 : (2 : F) = 0) (h00 : A 0 0 = 1) (h10 : A 1 0 = 0) (h20 : A 2 0 = 0)
    (hL : lowerBlock_hom A = 1) : A * A = 1 := by
  have e11 : A 1 1 = 1 := by simpa [lowerBlock_hom] using congrFun (congrFun hL 0) 0
  have e12 : A 1 2 = 0 := by simpa [lowerBlock_hom] using congrFun (congrFun hL 0) 1
  have e21 : A 2 1 = 0 := by simpa [lowerBlock_hom] using congrFun (congrFun hL 1) 0
  have e22 : A 2 2 = 1 := by simpa [lowerBlock_hom] using congrFun (congrFun hL 1) 1
  have e01 : A 0 1 + A 0 1 = 0 := by rw [← two_mul, h2, zero_mul]
  have e02 : A 0 2 + A 0 2 = 0 := by rw [← two_mul, h2, zero_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h10, h20, e11, e12, e21, e22, e01, e02]

private theorem exists_sl3_lowerBlock_hom (X : Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ D : Matrix.SpecialLinearGroup (Fin 3) F,
      (D : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 0 1 : Fin 3 → F) = Pi.single 0 1 ∧
        lowerBlock_hom (D : Matrix (Fin 3) (Fin 3) F) = (X : Matrix (Fin 2) (Fin 2) F) := by
  have hX : (X : Matrix (Fin 2) (Fin 2) F).det = 1 := Matrix.SpecialLinearGroup.det_coe X
  rw [Matrix.det_fin_two] at hX
  refine ⟨⟨!![1, 0, 0; 0, (X : Matrix (Fin 2) (Fin 2) F) 0 0, (X : Matrix (Fin 2) (Fin 2) F) 0 1;
    0, (X : Matrix (Fin 2) (Fin 2) F) 1 0, (X : Matrix (Fin 2) (Fin 2) F) 1 1], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_three]
    simp
    linear_combination hX
  · funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerBlock_hom]

theorem exists_hom_stabVec [Fintype F] (h2 : (2 : F) = 0) {w : Fin 3 → F} (hw : w ≠ 0) :
    ∃ ρ : ↥(stabVec w) →* SpecialLinearGroup (Fin 2) F, Function.Surjective ρ ∧
      ∀ g ∈ ρ.ker, g * g = 1 := by
  obtain ⟨g₀, hg₀⟩ := exists_sl3_mulVec_eq_single_hom hw
  have hinv : ((g₀⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (g₀ : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinv_e : ((g₀⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (Pi.single 0 1 : Fin 3 → F) = w := by
    rw [← hg₀, mulVec_mulVec, hinv, one_mulVec]
  have hfix : ∀ g : ↥(stabVec w),
      ((g₀ * (g : Matrix.SpecialLinearGroup (Fin 3) F) * g₀⁻¹ :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          (Pi.single 0 1 : Fin 3 → F) = Pi.single 0 1 := by
    intro g
    have hg : ((g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w :=
      mem_stabVec.mp g.2
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec,
      ← mulVec_mulVec, hinv_e, hg, hg₀]
  have hdet : ∀ g : ↥(stabVec w),
      (lowerBlock_hom ((g₀ * (g : Matrix.SpecialLinearGroup (Fin 3) F) * g₀⁻¹ :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).det = 1 := by
    intro g
    obtain ⟨c00, c10, c20⟩ := col_zero_hom (hfix g)
    rw [det_lowerBlock_hom c00 c10 c20]
    exact Matrix.SpecialLinearGroup.det_coe _
  obtain ⟨f, hf⟩ : ∃ f : ↥(stabVec w) → Matrix.SpecialLinearGroup (Fin 2) F,
      ∀ g : ↥(stabVec w), f g = ⟨lowerBlock_hom ((g₀ * (g : Matrix.SpecialLinearGroup (Fin 3) F) *
        g₀⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), hdet g⟩ :=
    ⟨fun g => ⟨lowerBlock_hom ((g₀ * (g : Matrix.SpecialLinearGroup (Fin 3) F) * g₀⁻¹ :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), hdet g⟩, fun g => rfl⟩
  have hmul : ∀ a b : ↥(stabVec w), f (a * b) = f a * f b := by
    intro a b
    obtain ⟨a00, a10, a20⟩ := col_zero_hom (hfix a)
    have e : g₀ * ((a * b : ↥(stabVec w)) : Matrix.SpecialLinearGroup (Fin 3) F) * g₀⁻¹ =
        (g₀ * (a : Matrix.SpecialLinearGroup (Fin 3) F) * g₀⁻¹) *
          (g₀ * (b : Matrix.SpecialLinearGroup (Fin 3) F) * g₀⁻¹) := by
      rw [Subgroup.coe_mul]
      group
    simp only [hf]
    have key : lowerBlock_hom ((g₀ * ((a * b : ↥(stabVec w)) : Matrix.SpecialLinearGroup (Fin 3) F) *
        g₀⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      lowerBlock_hom ((g₀ * (a : Matrix.SpecialLinearGroup (Fin 3) F) * g₀⁻¹ :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      lowerBlock_hom ((g₀ * (b : Matrix.SpecialLinearGroup (Fin 3) F) * g₀⁻¹ :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [e, Matrix.SpecialLinearGroup.coe_mul (g₀ * (a : Matrix.SpecialLinearGroup (Fin 3) F) * g₀⁻¹)
        (g₀ * (b : Matrix.SpecialLinearGroup (Fin 3) F) * g₀⁻¹)]
      exact lowerBlock_mul_hom a10 a20
    apply Subtype.ext
    exact key
  refine ⟨MonoidHom.mk' f hmul, ?_, ?_⟩
  ·
    intro X
    obtain ⟨D, hDe, hDX⟩ := exists_sl3_lowerBlock_hom X
    have hmem : (g₀⁻¹ * D * g₀ : Matrix.SpecialLinearGroup (Fin 3) F) ∈ stabVec w := by
      rw [mem_stabVec, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ← mulVec_mulVec, ← mulVec_mulVec, hg₀, hDe, hinv_e]
    refine ⟨⟨g₀⁻¹ * D * g₀, hmem⟩, ?_⟩
    show f ⟨g₀⁻¹ * D * g₀, hmem⟩ = X
    rw [hf]
    apply Subtype.ext
    have hc : g₀ * (g₀⁻¹ * D * g₀) * g₀⁻¹ = D := by group
    change lowerBlock_hom ((g₀ * (g₀⁻¹ * D * g₀) * g₀⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = (X : Matrix (Fin 2) (Fin 2) F)
    rw [hc]
    exact hDX
  ·
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hg' : f g = 1 := hg
    rw [hf] at hg'
    have hL := congrArg Subtype.val hg'
    change lowerBlock_hom ((g₀ * (g : Matrix.SpecialLinearGroup (Fin 3) F) * g₀⁻¹ :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (1 : Matrix (Fin 2) (Fin 2) F) at hL
    obtain ⟨c00, c10, c20⟩ := col_zero_hom (hfix g)
    have hAA := mul_self_eq_one_of_lowerBlock_hom h2 c00 c10 c20 hL
    have hcc : (g₀ * (g : Matrix.SpecialLinearGroup (Fin 3) F) * g₀⁻¹) *
        (g₀ * (g : Matrix.SpecialLinearGroup (Fin 3) F) * g₀⁻¹) = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
      exact hAA
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    have key : g₀ * ((g : Matrix.SpecialLinearGroup (Fin 3) F) *
        (g : Matrix.SpecialLinearGroup (Fin 3) F)) * g₀⁻¹ = 1 := by
      calc g₀ * ((g : Matrix.SpecialLinearGroup (Fin 3) F) *
            (g : Matrix.SpecialLinearGroup (Fin 3) F)) * g₀⁻¹
          = (g₀ * (g : Matrix.SpecialLinearGroup (Fin 3) F) * g₀⁻¹) *
              (g₀ * (g : Matrix.SpecialLinearGroup (Fin 3) F) * g₀⁻¹) := by group
        _ = 1 := hcc
    calc (g : Matrix.SpecialLinearGroup (Fin 3) F) * (g : Matrix.SpecialLinearGroup (Fin 3) F)
        = g₀⁻¹ * (g₀ * ((g : Matrix.SpecialLinearGroup (Fin 3) F) *
            (g : Matrix.SpecialLinearGroup (Fin 3) F)) * g₀⁻¹) * g₀ := by group
      _ = 1 := by rw [key]; group


end CFSG.Quasithin.H13.Ch4.CentK

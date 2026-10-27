module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthInAbs
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalEndNodeMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace SmallOrth

section Diag

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

open scoped Classical in
@[expose] noncomputable def pStar (δ : ι → Kˣ) : Matrix ι ι K :=
  Matrix.diagonal fun y => if δ y = 1 then 0 else 1

open scoped Classical in
@[expose] noncomputable def pOne (δ : ι → Kˣ) : Matrix ι ι K :=
  Matrix.diagonal fun y => if δ y = 1 then 1 else 0

theorem pStar_add_pOne (δ : ι → Kˣ) : pStar (K := K) δ + pOne δ = 1 := by
  ext y z
  simp only [pStar, pOne, Matrix.add_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : y = z
  · subst h
    by_cases hδ : δ y = 1 <;> simp [hδ]
  · simp [h]

theorem mul_pStar_comm {g : GL ι K} {δ : ι → Kˣ}
    (hg : g * TauCeti.diagGL δ = TauCeti.diagGL δ * g) :
    (g : Matrix ι ι K) * pStar δ = pStar δ * (g : Matrix ι ι K) := by
  have hm := TableBOrth.commute_diagGL_iff.mp hg
  ext y z
  rw [pStar, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hyz : δ y = δ z
  · rw [hyz]
    ring
  · have : (g : Matrix ι ι K) y z = 0 :=
      TableBOrth.eq_zero_of_commute_diagonal hm (fun h => hyz (Units.ext h))
    rw [this]
    ring

theorem inv_comm_diag {c : GL ι K} {δ : ι → Kˣ}
    (hcc : c * TauCeti.diagGL δ = TauCeti.diagGL δ * c) :
    c⁻¹ * TauCeti.diagGL δ = TauCeti.diagGL δ * c⁻¹ := by
  calc c⁻¹ * TauCeti.diagGL δ = c⁻¹ * (TauCeti.diagGL δ * c) * c⁻¹ := by group
    _ = c⁻¹ * (c * TauCeti.diagGL δ) * c⁻¹ := by rw [hcc]
    _ = TauCeti.diagGL δ * c⁻¹ := by group

@[expose] def fixStar (Ω : Subgroup (GL ι K)) (δ : ι → Kˣ) : Subgroup (GL ι K) where
  carrier := {g | g ∈ Ω ∧ g * TauCeti.diagGL δ = TauCeti.diagGL δ * g ∧
    (g : Matrix ι ι K) * pStar δ = pStar δ}
  mul_mem' := by
    rintro g g' ⟨hg, hgc, hgP⟩ ⟨hg', hg'c, hg'P⟩
    refine ⟨Ω.mul_mem hg hg', ?_, ?_⟩
    · rw [mul_assoc, hg'c, ← mul_assoc, hgc, mul_assoc]
    · rw [Units.val_mul, Matrix.mul_assoc, hg'P, hgP]
  one_mem' := ⟨Ω.one_mem, by rw [one_mul, mul_one], by rw [Units.val_one, Matrix.one_mul]⟩
  inv_mem' := by
    rintro g ⟨hg, hgc, hgP⟩
    refine ⟨Ω.inv_mem hg, inv_comm_diag hgc, ?_⟩
    have h1 : ((g⁻¹ : GL ι K) : Matrix ι ι K) * (g : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((g⁻¹ : GL ι K) : Matrix ι ι K) * pStar δ
        = ((g⁻¹ : GL ι K) : Matrix ι ι K) * ((g : Matrix ι ι K) * pStar δ) := by rw [hgP]
      _ = pStar δ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem fixStar_normal {Ω : Subgroup (GL ι K)} {δ : ι → Kˣ} {c : GL ι K} (hc : c ∈ Ω)
    (hcc : c * TauCeti.diagGL δ = TauCeti.diagGL δ * c) {g : GL ι K} (hg : g ∈ fixStar Ω δ) :
    c * g * c⁻¹ ∈ fixStar Ω δ := by
  obtain ⟨hgΩ, hgc, hgP⟩ := hg
  have hc' := inv_comm_diag hcc
  refine ⟨Ω.mul_mem (Ω.mul_mem hc hgΩ) (Ω.inv_mem hc), ?_, ?_⟩
  · calc c * g * c⁻¹ * TauCeti.diagGL δ = c * g * (c⁻¹ * TauCeti.diagGL δ) := by group
      _ = c * g * (TauCeti.diagGL δ * c⁻¹) := by rw [hc']
      _ = c * (g * TauCeti.diagGL δ) * c⁻¹ := by group
      _ = c * (TauCeti.diagGL δ * g) * c⁻¹ := by rw [hgc]
      _ = (c * TauCeti.diagGL δ) * g * c⁻¹ := by group
      _ = (TauCeti.diagGL δ * c) * g * c⁻¹ := by rw [hcc]
      _ = TauCeti.diagGL δ * (c * g * c⁻¹) := by group
  · have e1 := mul_pStar_comm hc'
    have e2 := mul_pStar_comm hcc
    have h1 : (c : Matrix ι ι K) * ((c⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K) * pStar δ
        = (c : Matrix ι ι K) * ((g : Matrix ι ι K) *
            (((c⁻¹ : GL ι K) : Matrix ι ι K) * pStar δ)) := by
          simp only [Units.val_mul, Matrix.mul_assoc]
      _ = (c : Matrix ι ι K) * ((g : Matrix ι ι K) *
            (pStar δ * ((c⁻¹ : GL ι K) : Matrix ι ι K))) := by rw [e1]
      _ = (c : Matrix ι ι K) * (((g : Matrix ι ι K) * pStar δ) *
            ((c⁻¹ : GL ι K) : Matrix ι ι K)) := by rw [Matrix.mul_assoc]
      _ = (c : Matrix ι ι K) * (pStar δ * ((c⁻¹ : GL ι K) : Matrix ι ι K)) := by rw [hgP]
      _ = ((c : Matrix ι ι K) * pStar δ) * ((c⁻¹ : GL ι K) : Matrix ι ι K) := by
          rw [Matrix.mul_assoc]
      _ = (pStar δ * (c : Matrix ι ι K)) * ((c⁻¹ : GL ι K) : Matrix ι ι K) := by rw [e2]
      _ = pStar δ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

theorem commute_of_fixStar {Ω : Subgroup (GL ι K)} {δ ε : ι → Kˣ}
    (hε : ∀ y, δ y = 1 → ε y = 1) {g : GL ι K} (hg : g ∈ fixStar Ω δ) :
    TauCeti.diagGL ε * g = g * TauCeti.diagGL ε := by
  obtain ⟨-, hgc, hgP⟩ := hg
  apply Units.ext
  set P : Matrix ι ι K := pStar δ with hP
  set x : Matrix ι ι K := Matrix.diagonal fun y => ((ε y : Kˣ) : K) with hx
  have hPQ : P + pOne δ = 1 := pStar_add_pOne δ
  have hQ : pOne (K := K) δ = 1 - P := eq_sub_of_add_eq' hPQ
  have hPg : P * (g : Matrix ι ι K) = P := by rw [← mul_pStar_comm hgc, hgP]
  have hxQ : x * pOne δ = pOne δ := by
    rw [hx, pOne, Matrix.diagonal_mul_diagonal]
    congr 1
    funext y
    by_cases hδ : δ y = 1
    · rw [if_pos hδ, hε y hδ, Units.val_one, one_mul]
    · simp [hδ]
  have hxP : x * P = P * x := by
    rw [hx, hP, pStar, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext y
    exact mul_comm _ _
  rw [hQ, mul_sub, Matrix.mul_one] at hxQ
  have E1 : x = (1 - P) + x * P := sub_eq_iff_eq_add.mp hxQ
  have hgx : ((TauCeti.diagGL ε * g : GL ι K) : Matrix ι ι K) = x * (g : Matrix ι ι K) := by
    rw [Units.val_mul, TauCeti.diagGL_coe]
  have hxg : ((g * TauCeti.diagGL ε : GL ι K) : Matrix ι ι K) = (g : Matrix ι ι K) * x := by
    rw [Units.val_mul, TauCeti.diagGL_coe]
  rw [hgx, hxg]
  have L : x * (g : Matrix ι ι K) = (g : Matrix ι ι K) - P + x * P := by
    calc x * (g : Matrix ι ι K) = ((1 - P) + x * P) * (g : Matrix ι ι K) :=
          congrArg (· * (g : Matrix ι ι K)) E1
      _ = (g : Matrix ι ι K) - P * (g : Matrix ι ι K) + x * (P * (g : Matrix ι ι K)) := by
          noncomm_ring
      _ = (g : Matrix ι ι K) - P + x * P := by rw [hPg]
  have R : (g : Matrix ι ι K) * x = (g : Matrix ι ι K) - P + x * P := by
    calc (g : Matrix ι ι K) * x = (g : Matrix ι ι K) * ((1 - P) + x * P) :=
          congrArg (fun y => (g : Matrix ι ι K) * y) E1
      _ = (g : Matrix ι ι K) - (g : Matrix ι ι K) * P + ((g : Matrix ι ι K) * (x * P)) := by
          noncomm_ring
      _ = (g : Matrix ι ι K) - P + (g : Matrix ι ι K) * (P * x) := by rw [hgP, hxP]
      _ = (g : Matrix ι ι K) - P + ((g : Matrix ι ι K) * P) * x := by rw [Matrix.mul_assoc]
      _ = (g : Matrix ι ι K) - P + P * x := by rw [hgP]
      _ = (g : Matrix ι ι K) - P + x * P := by rw [hxP]
  rw [L, R]

theorem commute_of_function {δ ε : ι → Kˣ} (hε : ∀ y z, δ y = δ z → ε y = ε z) {g : GL ι K}
    (hg : g * TauCeti.diagGL δ = TauCeti.diagGL δ * g) :
    TauCeti.diagGL ε * g = g * TauCeti.diagGL ε := by
  have hm := TableBOrth.commute_diagGL_iff.mp hg
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, TauCeti.diagGL_coe]
  ext y z
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hyz : δ y = δ z
  · rw [hε y z hyz]
    ring
  · have : (g : Matrix ι ι K) y z = 0 :=
      TableBOrth.eq_zero_of_commute_diagonal hm (fun h => hyz (Units.ext h))
    rw [this]
    ring

theorem diag_mul_pStar {δ ε : ι → Kˣ} (h : ∀ y, δ y ≠ 1 → ε y = 1) :
    (TauCeti.diagGL ε : Matrix ι ι K) * pStar δ = pStar δ := by
  rw [TauCeti.diagGL_coe, pStar, Matrix.diagonal_mul_diagonal]
  congr 1
  funext y
  by_cases hδ : δ y = 1
  · simp [hδ]
  · simp [hδ, h y hδ]

end Diag

end SmallOrth

end CFSG.StandardType

end

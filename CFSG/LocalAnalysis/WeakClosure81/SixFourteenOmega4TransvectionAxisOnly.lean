module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenOmega4TransvectionUnique
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenOmega4UniqueAbstract
public import CFSG.Quasithin.Vol2.Ch9H11Norm

public section

noncomputable section

open CFSG.Quasithin CFSG.ASVolI.ChH
open CFSG.Quasithin.H13.H11P
open CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix

namespace CFSG.LocalAnalysis.WeakClosure81

local notation "F₄" => GaloisField 2 2
local notation "M₄" => Matrix (Fin 2) (Fin 2) F₄

lemma fixed_iff_isSymm_mul (P : SL₂ F₄) (X : M₄) :
    (P : M₄) * Xᵀ * (((P⁻¹ : SL₂ F₄) : M₄))ᵀ = X ↔
      Matrix.IsSymm (((P⁻¹ : SL₂ F₄) : M₄) * X) := by
  have hQP : ((P⁻¹ : SL₂ F₄) : M₄) * (P : M₄) = 1 := coe_inv_mul_coe P
  have hPQ : (P : M₄) * ((P⁻¹ : SL₂ F₄) : M₄) = 1 := coe_mul_coe_inv P
  constructor
  · intro h
    rw [Matrix.IsSymm, Matrix.transpose_mul]
    have h1 : ((P⁻¹ : SL₂ F₄) : M₄) * X =
        Xᵀ * (((P⁻¹ : SL₂ F₄) : M₄))ᵀ := by
      calc ((P⁻¹ : SL₂ F₄) : M₄) * X
          = ((P⁻¹ : SL₂ F₄) : M₄) *
              ((P : M₄) * Xᵀ * (((P⁻¹ : SL₂ F₄) : M₄))ᵀ) := by rw [h]
        _ = (((P⁻¹ : SL₂ F₄) : M₄) * (P : M₄)) * Xᵀ *
              (((P⁻¹ : SL₂ F₄) : M₄))ᵀ := by simp only [Matrix.mul_assoc]
        _ = Xᵀ * (((P⁻¹ : SL₂ F₄) : M₄))ᵀ := by rw [hQP, Matrix.one_mul]
    rw [h1]
  · intro h
    rw [Matrix.IsSymm, Matrix.transpose_mul] at h
    calc (P : M₄) * Xᵀ * (((P⁻¹ : SL₂ F₄) : M₄))ᵀ
        = (P : M₄) * (Xᵀ * (((P⁻¹ : SL₂ F₄) : M₄))ᵀ) := by
          rw [Matrix.mul_assoc]
      _ = (P : M₄) * (((P⁻¹ : SL₂ F₄) : M₄) * X) := by rw [h]
      _ = ((P : M₄) * ((P⁻¹ : SL₂ F₄) : M₄)) * X := by
          rw [← Matrix.mul_assoc]
      _ = X := by rw [hPQ, Matrix.one_mul]

lemma mem_fixVSub_rho_trn_iff {t : MulAut (VM F₄)} {P : SL₂ F₄}
    (ht : IsFTransvectionOn F₄ M₄ t) (hP : t = rho (P, P⁻¹) * trn) (X : M₄) :
    X ∈ fixVSub (F := F₄) (M := M₄) t ↔
      Matrix.IsSymm (((P⁻¹ : SL₂ F₄) : M₄) * X) := by
  obtain ⟨g, hg, -, -⟩ := ht
  rw [← hg, fixVSub_linToMulAut g, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]
  have hgX : g.toLinearMap X = addMap t X := by
    rw [← addMap_linToMulAut_apply g X, hg]
  rw [hgX, hP, addMap_mul, addMap_rho, addMap_trn]
  exact fixed_iff_isSymm_mul P X

lemma eq_one_of_forall_isSymm_mul_isSymm {A : M₄} (hdet : Matrix.det A = 1)
    (h : ∀ Y : M₄, Matrix.IsSymm Y → Matrix.IsSymm (A * Y)) : A = 1 := by
  have hA : Matrix.IsSymm A := by
    simpa using h 1 Matrix.isSymm_one
  have hE : Matrix.IsSymm (A * Matrix.single 0 0 (1 : F₄)) :=
    h _ (Matrix.IsSymm.ext (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]))
  have hAlt : Matrix.IsSymm
      (A * (Matrix.single 0 1 (1 : F₄) + Matrix.single 1 0 (1 : F₄))) :=
    h _ (Matrix.IsSymm.ext (by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.add_apply, Matrix.single_apply]))
  have h10 : A 1 0 = A 0 1 := Matrix.IsSymm.apply hA 0 1
  have h10' : A 1 0 = 0 := by
    have := Matrix.IsSymm.apply hE 0 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply] using this
  have h01 : A 0 1 = 0 := h10.symm.trans h10'
  have h11 : A 1 1 = A 0 0 := by
    have := Matrix.IsSymm.apply hAlt 0 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.single_apply] using this
  have hsq : (A 0 0) ^ 2 = 1 := by
    rw [Matrix.det_fin_two] at hdet
    rw [h10', h01, h11] at hdet
    simpa [pow_two] using hdet
  have h00 : A 0 0 = 1 := eq_one_of_sq_eq_one hsq
  have h11' : A 1 1 = 1 := h11.trans h00
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10', h11']

theorem ncard_fTransvectionSet_fixed_axis_le_one
    (H : Submodule F₄ M₄) (hH : Module.finrank F₄ H = 3) :
    Nat.card { t : MulAut (VM F₄) |
      t ∈ Subgroup.normalizer ((Lm F₄ : Subgroup (MulAut (VM F₄))) : Set (MulAut (VM F₄)))
      ∧ IsFTransvectionOn F₄ M₄ t
      ∧ fixVSub (F := F₄) (M := M₄) t = H } ≤ 1 := by
  classical
  have hsub : Subsingleton { t : MulAut (VM F₄) |
      t ∈ Subgroup.normalizer ((Lm F₄ : Subgroup (MulAut (VM F₄))) : Set (MulAut (VM F₄)))
      ∧ IsFTransvectionOn F₄ M₄ t
      ∧ fixVSub (F := F₄) (M := M₄) t = H } := by
    refine ⟨fun a b => ?_⟩
    apply Subtype.ext
    obtain ⟨P₁, hP₁⟩ := exists_P_eq_rho_trn a.2.1 a.2.2.1
    obtain ⟨P₂, hP₂⟩ := exists_P_eq_rho_trn b.2.1 b.2.2.1
    let Q₂ : M₄ := ((P₂⁻¹ : SL₂ F₄) : M₄)
    let M : M₄ := Q₂ * (P₁ : M₄)
    have hsymm : ∀ Y : M₄, Matrix.IsSymm Y → Matrix.IsSymm (M * Y) := by
      intro Y hY
      have h1 : (P₁ : M₄) * Y ∈
          fixVSub (F := F₄) (M := M₄) (a : MulAut (VM F₄)) :=
        (mem_fixVSub_rho_trn_iff a.2.2.1 hP₁ ((P₁ : M₄) * Y)).mpr (by
          rw [show ((P₁⁻¹ : SL₂ F₄) : M₄) * ((P₁ : M₄) * Y) = Y by
            rw [← Matrix.mul_assoc, coe_inv_mul_coe, Matrix.one_mul]]
          exact hY)
      have h2 : (P₁ : M₄) * Y ∈
          fixVSub (F := F₄) (M := M₄) (b : MulAut (VM F₄)) := by
        rw [b.2.2.2]
        rw [a.2.2.2] at h1
        exact h1
      have h3 : Matrix.IsSymm (Q₂ * ((P₁ : M₄) * Y)) :=
        (mem_fixVSub_rho_trn_iff b.2.2.1 hP₂ ((P₁ : M₄) * Y)).mp h2
      simpa only [M, Matrix.mul_assoc] using h3
    have hdet : Matrix.det M = 1 := by
      change Matrix.det (((P₂⁻¹ : SL₂ F₄) : M₄) * (P₁ : M₄)) = 1
      rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe,
        Matrix.SpecialLinearGroup.det_coe, one_mul]
    have hM : M = 1 := eq_one_of_forall_isSymm_mul_isSymm hdet hsymm
    have hQ : Q₂ * (P₁ : M₄) = 1 := by simpa only [M] using hM
    have hP : (P₁ : M₄) = (P₂ : M₄) := by
      have h3 : (P₂ : M₄) * (Q₂ * (P₁ : M₄)) = (P₂ : M₄) := by
        rw [hQ, Matrix.mul_one]
      rw [show (P₂ : M₄) * (Q₂ * (P₁ : M₄)) = (P₁ : M₄) from by
        rw [← Matrix.mul_assoc]
        rw [show (P₂ : M₄) * Q₂ = 1 by simpa only [Q₂] using coe_mul_coe_inv P₂]
        rw [Matrix.one_mul]] at h3
      exact h3
    have hPsub : P₁ = P₂ := Subtype.ext hP
    calc (a : MulAut (VM F₄)) = rho (P₁, P₁⁻¹) * trn := hP₁
      _ = rho (P₂, P₂⁻¹) * trn := by rw [hPsub]
      _ = (b : MulAut (VM F₄)) := hP₂.symm
  haveI : Finite { t : MulAut (VM F₄) |
      t ∈ Subgroup.normalizer ((Lm F₄ : Subgroup (MulAut (VM F₄))) : Set (MulAut (VM F₄)))
      ∧ IsFTransvectionOn F₄ M₄ t
      ∧ fixVSub (F := F₄) (M := M₄) t = H } := Subtype.finite
  rw [Finite.card_le_one_iff_subsingleton]
  exact hsub

end CFSG.LocalAnalysis.WeakClosure81

end

end

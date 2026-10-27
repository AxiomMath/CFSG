module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentSL5
import CFSG.ClassicalInvolution.Phan.AutSU2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Matrix

@[expose] def dM : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![0, 1; -2, 0]

theorem dM_mul_psiM : dM * psiM = 1 := by decide

theorem psiM_mul_dM : psiM * dM = 1 := by decide

theorem det_dM : dM.det = 2 := by decide

theorem det_psiM_mul_dM (x : SL5) :
    (psiM * (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * dM).det = 1 := by
  rw [det_mul, det_mul, x.2, mul_one, ← det_mul, psiM_mul_dM, det_one]

theorem det_dM_mul_psiM (x : SL5) :
    (dM * (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM).det = 1 := by
  rw [det_mul, det_mul, x.2, mul_one, ← det_mul, dM_mul_psiM, det_one]

@[expose] def deltaAut : SL5 ≃* SL5 where
  toFun x := ⟨psiM * x * dM, det_psiM_mul_dM x⟩
  invFun x := ⟨dM * x * psiM, det_dM_mul_psiM x⟩
  left_inv x := by
    apply Subtype.ext
    change dM * (psiM * (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * dM) * psiM = x
    simp only [Matrix.mul_assoc, dM_mul_psiM, Matrix.mul_one]
    rw [← Matrix.mul_assoc, dM_mul_psiM, Matrix.one_mul]
  right_inv x := by
    apply Subtype.ext
    change psiM * (dM * (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM) * dM = x
    simp only [Matrix.mul_assoc, psiM_mul_dM, Matrix.mul_one]
    rw [← Matrix.mul_assoc, psiM_mul_dM, Matrix.one_mul]
  map_mul' x y := by
    apply Subtype.ext
    change psiM * ((x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * y) * dM =
      (psiM * x * dM) * (psiM * y * dM)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc dM psiM, dM_mul_psiM, Matrix.one_mul]

@[simp] theorem coe_deltaAut (x : SL5) :
    ((deltaAut x : SL5) : Matrix (Fin 2) (Fin 2) (ZMod 5)) = psiM * x * dM := rfl

private theorem sl5_forall {P : Matrix (Fin 2) (Fin 2) (ZMod 5) → Prop}
    (h : ∀ a b c d : ZMod 5, a * d - b * c = 1 → P !![a, b; c, d]) (x : SL5) :
    P (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) := by
  have hx := x.2
  rw [det_fin_two] at hx
  rw [eta_fin_two (x : Matrix (Fin 2) (Fin 2) (ZMod 5))]
  exact h _ _ _ _ hx

@[simp] theorem deltaAut_deltaAut (x : SL5) : deltaAut (deltaAut x) = x := by
  apply Subtype.ext
  rw [coe_deltaAut, coe_deltaAut]
  exact sl5_forall (P := fun X => psiM * (psiM * X * dM) * dM = X) (by decide +kernel) x

theorem deltaAut_hM : deltaAut hM = hM⁻¹ := by
  rw [← neg_hM]
  decide

theorem deltaAut_cM : deltaAut cM = cM * hM := by decide

theorem mul_deltaAut_ne_neg_one (y : SL5) : y * deltaAut y ≠ -1 := by
  intro h
  have h' : (y : Matrix (Fin 2) (Fin 2) (ZMod 5)) * (psiM * y * dM) = -1 :=
    congrArg (fun z : SL5 => (z : Matrix (Fin 2) (Fin 2) (ZMod 5))) h
  exact sl5_forall (P := fun X => X * (psiM * X * dM) ≠ -1) (by decide +kernel) y h'

private def lengList : List (Matrix (Fin 2) (Fin 2) (ZMod 5)) :=
  [!![1, 0; 0, 1], !![0, 1; 4, 2], !![1, 0; 1, 1], !![1, 0; 4, 1], !![0, 1; 4, 3],
   !![0, 1; 4, 0], !![1, 3; 4, 3], !![0, 2; 2, 3], !![0, 2; 2, 2], !![1, 1; 4, 0],
   !![0, 2; 2, 0], !![1, 4; 0, 1], !![0, 1; 4, 4], !![0, 1; 4, 1], !![1, 1; 0, 1],
   !![1, 2; 4, 4], !![0, 2; 2, 4], !![1, 3; 0, 1], !![1, 2; 0, 1], !![0, 2; 2, 1]]

theorem exists_mul_eq_deltaAut {p : SL5} (hp : p * deltaAut p = 1) :
    ∃ r : SL5, r * p = deltaAut r := by
  have hp' : (p : Matrix (Fin 2) (Fin 2) (ZMod 5)) * (psiM * p * dM) = 1 :=
    congrArg (fun z : SL5 => (z : Matrix (Fin 2) (Fin 2) (ZMod 5))) hp
  obtain ⟨r, -, hr, hrdet⟩ := sl5_forall
    (P := fun X => X * (psiM * X * dM) = 1 →
      ∃ r ∈ lengList, r * X = psiM * r * dM ∧ r.det = 1) (by decide +kernel) p hp'
  exact ⟨⟨r, hrdet⟩, Subtype.ext hr⟩

theorem not_conj_deltaAut_fix_hM_cM (m : SL5) :
    ¬ (m * deltaAut hM = hM * m ∧ m * deltaAut cM = cM * m) := by
  rintro ⟨h₁, h₂⟩
  let M : Matrix (Fin 2) (Fin 2) (ZMod 5) := m
  have h₁' : M * (psiM * !![2, 0; 0, 3] * dM) = !![2, 0; 0, 3] * M :=
    congrArg (fun z : SL5 => (z : Matrix (Fin 2) (Fin 2) (ZMod 5))) h₁
  have h₂' : M * (psiM * !![0, -1; 1, 0] * dM) = !![0, -1; 1, 0] * M :=
    congrArg (fun z : SL5 => (z : Matrix (Fin 2) (Fin 2) (ZMod 5))) h₂
  exact sl5_forall (P := fun X => ¬ (X * (psiM * !![2, 0; 0, 3] * dM) = !![2, 0; 0, 3] * X ∧
    X * (psiM * !![0, -1; 1, 0] * dM) = !![0, -1; 1, 0] * X)) (by decide +kernel) m ⟨h₁', h₂'⟩

private theorem exists_sq_mul_eq_one (u : ZMod 5) (hu : u ≠ 0) :
    (∃ s : ZMod 5, s ^ 2 * u = 1) ∨ ∃ s : ZMod 5, s ^ 2 * (u * 2) = 1 := by
  revert u
  decide

private theorem eq_conj_of_mul_eq (α f : SL5 → SL5) (M : Matrix (Fin 2) (Fin 2) (ZMod 5))
    (hM1 : M.det = 1)
    (hα : ∀ y, ((α y : SL5) : Matrix (Fin 2) (Fin 2) (ZMod 5)) * M = M * (f y : SL5)) :
    ∃ g : SL5, ∀ y, α y = g * f y * g⁻¹ :=
  ⟨⟨M, hM1⟩, fun y => eq_mul_inv_of_mul_eq (Subtype.ext (hα y))⟩

theorem exists_eq_conj_or_conj_deltaAut (α : MulAut SL5) :
    ∃ g : SL5, (∀ y, α y = g * y * g⁻¹) ∨ (∀ y, α y = g * deltaAut y * g⁻¹) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨A, ψ, hA⟩ := CFSG.ClassicalInvolution.Phan.exists_toGL_eq_conj_map α
  have hψ : ∀ y : SL5, Matrix.SpecialLinearGroup.map (ψ : ZMod 5 →+* ZMod 5) y = y := by
    intro y
    rw [Subsingleton.elim (ψ : ZMod 5 →+* ZMod 5) (RingHom.id _)]
    ext i j
    simp
  have key : ∀ y : SL5, ((α y : SL5) : Matrix (Fin 2) (Fin 2) (ZMod 5)) * (A : Matrix _ _ _) =
      (A : Matrix _ _ _) * (y : Matrix _ _ _) := by
    intro y
    have h := congrArg (fun B : GL (Fin 2) (ZMod 5) => ((B * A : GL (Fin 2) (ZMod 5)) :
      Matrix (Fin 2) (Fin 2) (ZMod 5))) (hA y)
    simpa [hψ, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, mul_assoc] using h
  have hdet : (A : Matrix (Fin 2) (Fin 2) (ZMod 5)).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit A) |>.ne_zero
  rcases exists_sq_mul_eq_one _ hdet with ⟨s, hs⟩ | ⟨s, hs⟩
  · obtain ⟨g, hg⟩ := eq_conj_of_mul_eq α id (s • (A : Matrix _ _ _))
      (by rw [det_smul, Fintype.card_fin, hs])
      (fun y => by rw [Matrix.mul_smul, Matrix.smul_mul, key]; rfl)
    exact ⟨g, Or.inl hg⟩
  · obtain ⟨g, hg⟩ := eq_conj_of_mul_eq α deltaAut (s • ((A : Matrix _ _ _) * dM))
      (by
        rw [det_smul, Fintype.card_fin, det_mul, det_dM, ← hs])
      (fun y => by
        rw [coe_deltaAut, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, key]
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc dM psiM, dM_mul_psiM, Matrix.one_mul])
    exact ⟨g, Or.inr hg⟩

end CFSG.OddTranspositions.PartThree.Wong

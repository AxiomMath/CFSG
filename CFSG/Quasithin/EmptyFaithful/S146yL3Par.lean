module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualLin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification Matrix

namespace CFSG.Quasithin

abbrev SL3F2 : Type := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

section Q3

open CFSG.QuasithinUnique.Setup.X7a

theorem mem_Q3_zero_iff (g : SL3F2) :
    g ∈ Q3 (ZMod 2) 0 ↔
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 := by
  have hQ : Q3 (ZMod 2) 0 = stabilizer (flagSpace 3 (ZMod 2) 1) := rfl
  rw [hQ]
  constructor
  · intro hg
    have hg' := mem_stabilizer.mp hg
    have hmem : (Pi.single 0 1 : Fin 3 → ZMod 2) ∈ flagSpace 3 (ZMod 2) 1 := by
      rw [mem_flagSpace]
      intro j hj
      have : j ≠ 0 := by
        intro h; subst h; simp at hj
      simp [this]
    have h1 : mulVecLin (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (Pi.single 0 1) ∈
        (flagSpace 3 (ZMod 2) 1).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) :=
      Submodule.mem_map_of_mem hmem
    rw [hg', mem_flagSpace] at h1
    have e1 := h1 1 (by decide)
    have e2 := h1 2 (by decide)
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at e1 e2
    exact ⟨e1, e2⟩
  · rintro ⟨h1, h2⟩
    apply mem_stabilizer_of_map_le
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    rw [mem_flagSpace] at hv
    rw [Submodule.mem_comap, mem_flagSpace]
    intro j hj
    have hv1 := hv 1 (by decide)
    have hv2 := hv 2 (by decide)
    have : j = 1 ∨ j = 2 := by
      fin_cases j <;> simp at hj ⊢
    rcases this with rfl | rfl
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, hv1, hv2]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h2, hv1, hv2]

theorem mem_Q3_one_iff (g : SL3F2) :
    g ∈ Q3 (ZMod 2) 1 ↔
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0 := by
  have hQ : Q3 (ZMod 2) 1 = stabilizer (flagSpace 3 (ZMod 2) 2) := rfl
  rw [hQ]
  constructor
  · intro hg
    have hg' := mem_stabilizer.mp hg
    have hmem : ∀ i : Fin 3, i ≠ 2 → (Pi.single i 1 : Fin 3 → ZMod 2) ∈ flagSpace 3 (ZMod 2) 2 := by
      intro i hi
      rw [mem_flagSpace]
      intro j hj
      have hj2 : j = 2 := by
        fin_cases j <;> simp at hj ⊢
      subst hj2
      simp [Ne.symm hi]
    have h0 := hmem 0 (by decide)
    have h1 := hmem 1 (by decide)
    have e0 : mulVecLin (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (Pi.single 0 1) ∈
        (flagSpace 3 (ZMod 2) 2).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) :=
      Submodule.mem_map_of_mem h0
    have e1 : mulVecLin (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (Pi.single 1 1) ∈
        (flagSpace 3 (ZMod 2) 2).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) :=
      Submodule.mem_map_of_mem h1
    rw [hg', mem_flagSpace] at e0 e1
    have f0 := e0 2 (by decide)
    have f1 := e1 2 (by decide)
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at f0 f1
    exact ⟨f0, f1⟩
  · rintro ⟨h0, h1⟩
    apply mem_stabilizer_of_map_le
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    rw [mem_flagSpace] at hv
    rw [Submodule.mem_comap, mem_flagSpace]
    intro j hj
    have hv2 := hv 2 (by decide)
    have hj2 : j = 2 := by
      fin_cases j <;> simp at hj ⊢
    subst hj2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, h1, hv2]

end Q3

section Fixes

@[expose] def FixesVec (H : Subgroup SL3F2) : Prop :=
  ∃ w : Fin 3 → ZMod 2, w ≠ 0 ∧ ∀ h ∈ H, (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w = w

@[expose] def FixesCov (H : Subgroup SL3F2) : Prop :=
  ∃ φ : Fin 3 → ZMod 2, φ ≠ 0 ∧ ∀ h ∈ H, φ ᵥ* (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) = φ

theorem fixesVec_map_slConj (A : GL (Fin 3) (ZMod 2)) (H : Subgroup SL3F2) :
    FixesVec (H.map (CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) A).toMonoidHom) ↔
      FixesVec H := by
  have hAi : ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := Units.inv_mul A
  have hiA : (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := Units.mul_inv A
  constructor
  · rintro ⟨w', hw', hfix⟩
    refine ⟨((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w', ?_, fun h hh => ?_⟩
    · intro h0
      apply hw'
      have := congrArg (fun v => (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) h0
      simpa [Matrix.mulVec_mulVec, hiA] using this
    · have h1 := hfix _ (Subgroup.mem_map_of_mem _ hh)
      change ((CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) A h : SL3F2) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w' = w' at h1
      rw [LinearFlag.coe_slConjugation] at h1
      have h2 := congrArg (fun v => ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) h1
      simp only [Matrix.mulVec_mulVec] at h2
      have e : ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) =
          (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAi, Matrix.one_mul]
      rw [e, ← Matrix.mulVec_mulVec] at h2
      exact h2
  · rintro ⟨w, hw, hfix⟩
    refine ⟨(A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w, ?_, ?_⟩
    · intro h0
      apply hw
      have := congrArg (fun v => ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) h0
      simpa [Matrix.mulVec_mulVec, hAi] using this
    · intro y hy
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hy
      change ((CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) A h : SL3F2) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ _ = _
      rw [LinearFlag.coe_slConjugation]
      have e : (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
        rw [Matrix.mul_assoc _ (((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))),
          hAi, Matrix.mul_one]
      rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, hfix h hh]

theorem fixesCov_map_slConj (A : GL (Fin 3) (ZMod 2)) (H : Subgroup SL3F2) :
    FixesCov (H.map (CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) A).toMonoidHom) ↔
      FixesCov H := by
  have hAi : ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := Units.inv_mul A
  have hiA : (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := Units.mul_inv A
  constructor
  · rintro ⟨φ', hφ', hfix⟩
    refine ⟨φ' ᵥ* (A : Matrix (Fin 3) (Fin 3) (ZMod 2)), ?_, fun h hh => ?_⟩
    · intro h0
      apply hφ'
      have := congrArg (fun v => v ᵥ* ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) h0
      simpa [Matrix.vecMul_vecMul, hiA] using this
    · have h1 := hfix _ (Subgroup.mem_map_of_mem _ hh)
      change φ' ᵥ* ((CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) A h : SL3F2) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) = φ' at h1
      rw [LinearFlag.coe_slConjugation] at h1
      have h2 := congrArg (fun v => v ᵥ* (A : Matrix (Fin 3) (Fin 3) (ZMod 2))) h1
      simp only [Matrix.vecMul_vecMul] at h2
      have e : (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
        rw [Matrix.mul_assoc _ (((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))),
          hAi, Matrix.mul_one]
      rw [e, ← Matrix.vecMul_vecMul] at h2
      exact h2
  · rintro ⟨φ, hφ, hfix⟩
    refine ⟨φ ᵥ* ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)), ?_, ?_⟩
    · intro h0
      apply hφ
      have := congrArg (fun v => v ᵥ* (A : Matrix (Fin 3) (Fin 3) (ZMod 2))) h0
      simpa [Matrix.vecMul_vecMul, hAi] using this
    · intro y hy
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hy
      change _ ᵥ* ((CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) A h : SL3F2) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
      rw [LinearFlag.coe_slConjugation]
      have e : ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) =
          (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAi, Matrix.one_mul]
      rw [Matrix.vecMul_vecMul, e, ← Matrix.vecMul_vecMul, hfix h hh]

theorem fixesVec_iff_fixesCov_map_tau (H : Subgroup SL3F2) :
    FixesVec H ↔
      FixesCov (H.map (CatalogueBGraphForm.slGraphAut 3 (ZMod 2)).toMonoidHom) := by
  constructor
  · rintro ⟨w, hw, hfix⟩
    refine ⟨w, hw, fun y hy => ?_⟩
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hy
    change w ᵥ* ((CatalogueBGraphForm.slGraphAut 3 (ZMod 2) h : SL3F2) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = w
    rw [CatalogueBGraphForm.slGraphAut_matrix, Matrix.vecMul_transpose]
    exact hfix _ (H.inv_mem hh)
  · rintro ⟨φ, hφ, hfix⟩
    refine ⟨φ, hφ, fun h hh => ?_⟩
    have h1 := hfix _ (Subgroup.mem_map_of_mem _ (H.inv_mem hh))
    change φ ᵥ* ((CatalogueBGraphForm.slGraphAut 3 (ZMod 2) (h⁻¹) : SL3F2) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = φ at h1
    rw [CatalogueBGraphForm.slGraphAut_matrix, inv_inv, Matrix.vecMul_transpose] at h1
    exact h1

theorem fixesCov_iff_fixesVec_map_tau (H : Subgroup SL3F2) :
    FixesCov H ↔
      FixesVec (H.map (CatalogueBGraphForm.slGraphAut 3 (ZMod 2)).toMonoidHom) := by
  constructor
  · rintro ⟨φ, hφ, hfix⟩
    refine ⟨φ, hφ, fun y hy => ?_⟩
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hy
    change ((CatalogueBGraphForm.slGraphAut 3 (ZMod 2) h : SL3F2) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ φ = φ
    rw [CatalogueBGraphForm.slGraphAut_matrix, Matrix.mulVec_transpose]
    exact hfix _ (H.inv_mem hh)
  · rintro ⟨w, hw, hfix⟩
    refine ⟨w, hw, fun h hh => ?_⟩
    have h1 := hfix _ (Subgroup.mem_map_of_mem _ (H.inv_mem hh))
    change ((CatalogueBGraphForm.slGraphAut 3 (ZMod 2) (h⁻¹) : SL3F2) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w = w at h1
    rw [CatalogueBGraphForm.slGraphAut_matrix, inv_inv, Matrix.mulVec_transpose] at h1
    exact h1

end Fixes

section Facts

open CFSG.QuasithinUnique.Setup.X7a

theorem det_col0 (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hdet : M.det = 1) (h10 : M 1 0 = 0)
    (h20 : M 2 0 = 0) : M 0 0 = 1 := by
  have key : ∀ a b c d e f g h i : ZMod 2,
      a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g = 1 → d = 0 → g = 0 →
        a = 1 := by decide
  rw [Matrix.det_fin_three] at hdet
  exact key _ _ _ _ _ _ _ _ _ hdet h10 h20

theorem det_row2 (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hdet : M.det = 1) (h20 : M 2 0 = 0)
    (h21 : M 2 1 = 0) : M 2 2 = 1 := by
  have key : ∀ a b c d e f g h i : ZMod 2,
      a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g = 1 → g = 0 → h = 0 →
        i = 1 := by decide
  rw [Matrix.det_fin_three] at hdet
  exact key _ _ _ _ _ _ _ _ _ hdet h20 h21

@[expose] def tr01 : SL3F2 := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩
@[expose] def tr12 : SL3F2 := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩
@[expose] def tr21 : SL3F2 := ⟨!![1, 0, 0; 0, 1, 0; 0, 1, 1], by decide⟩
@[expose] def tr10 : SL3F2 := ⟨!![1, 0, 0; 1, 1, 0; 0, 0, 1], by decide⟩
@[expose] def tr02 : SL3F2 := ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩
@[expose] def tr20 : SL3F2 := ⟨!![1, 0, 0; 0, 1, 0; 1, 0, 1], by decide⟩

theorem fixesVec_Q3_zero : FixesVec (Q3 (ZMod 2) 0) := by
  refine ⟨![1, 0, 0], by decide, fun h hh => ?_⟩
  obtain ⟨h10, h20⟩ := (mem_Q3_zero_iff h).mp hh
  have h00 := det_col0 (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) h.2 h10 h20
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h00, h10, h20]

theorem fixesCov_Q3_one : FixesCov (Q3 (ZMod 2) 1) := by
  refine ⟨![0, 0, 1], by decide, fun h hh => ?_⟩
  obtain ⟨h20, h21⟩ := (mem_Q3_one_iff h).mp hh
  have h22 := det_row2 (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) h.2 h20 h21
  funext i
  fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, h20, h21, h22]

theorem not_fixesCov_Q3_zero : ¬ FixesCov (Q3 (ZMod 2) 0) := by
  rintro ⟨φ, hφ, hfix⟩
  have h1 := hfix tr01 ((mem_Q3_zero_iff _).mpr ⟨by decide, by decide⟩)
  have h2 := hfix tr12 ((mem_Q3_zero_iff _).mpr ⟨by decide, by decide⟩)
  have h3 := hfix tr21 ((mem_Q3_zero_iff _).mpr ⟨by decide, by decide⟩)
  have key : ∀ φ : Fin 3 → ZMod 2,
      φ ᵥ* (tr01 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = φ →
      φ ᵥ* (tr12 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = φ →
      φ ᵥ* (tr21 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = φ → φ = 0 := by decide
  exact hφ (key φ h1 h2 h3)

theorem not_fixesVec_Q3_one : ¬ FixesVec (Q3 (ZMod 2) 1) := by
  rintro ⟨w, hw, hfix⟩
  have h1 := hfix tr01 ((mem_Q3_one_iff _).mpr ⟨by decide, by decide⟩)
  have h2 := hfix tr10 ((mem_Q3_one_iff _).mpr ⟨by decide, by decide⟩)
  have h3 := hfix tr02 ((mem_Q3_one_iff _).mpr ⟨by decide, by decide⟩)
  have key : ∀ w : Fin 3 → ZMod 2,
      (tr01 : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w = w →
      (tr10 : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w = w →
      (tr02 : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w = w → w = 0 := by decide
  exact hw (key w h1 h2 h3)

theorem Q3_zero_ne_top : Q3 (ZMod 2) 0 ≠ ⊤ := fun h => by
  have h1 : tr10 ∈ Q3 (ZMod 2) 0 := h ▸ Subgroup.mem_top _
  have h2 := (mem_Q3_zero_iff _).mp h1
  revert h2
  decide

theorem Q3_one_ne_top : Q3 (ZMod 2) 1 ≠ ⊤ := fun h => by
  have h1 : tr20 ∈ Q3 (ZMod 2) 1 := h ▸ Subgroup.mem_top _
  have h2 := (mem_Q3_one_iff _).mp h1
  revert h2
  decide

end Facts

section Classification

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X7a

theorem exists_conj_map_eq_of_isSylowTwoOf {X : Type*} [Group X] [Finite X] {U T : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) (hT : IsSylowTwoOf T ⊤) :
    ∃ g : X, U.map (MulAut.conj g).toMonoidHom = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUi : ¬ 2 ∣ U.index := by
    have h1 : (U.subgroupOf (⊤ : Subgroup X)).index = U.index := Subgroup.relIndex_top_right U
    rw [← h1]
    exact hU.2.2
  have hTi : ¬ 2 ∣ T.index := by
    have h1 : (T.subgroupOf (⊤ : Subgroup X)).index = T.index := Subgroup.relIndex_top_right T
    rw [← h1]
    exact hT.2.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hU.2.1.toSylow hUi) (hT.2.1.toSylow hTi)
  refine ⟨g, ?_⟩
  have := congrArg (fun P : Sylow 2 X => (P : Subgroup X)) hg
  simpa [LinearFlag.coe_sylow_smul] using this

theorem upperTriangular_le_Q3_two (j : Fin 2) : upperTriangular 3 (ZMod 2) ≤ Q3 (ZMod 2) j := by
  rw [Q3_eq]
  exact upperTriangular_le_flagStabilizer _

theorem isMaxParabolic2_eq_map_Q3 {P : Subgroup SL3F2} (hP : IsMaxParabolic2 (⊤ : Subgroup SL3F2) P) :
    ∃ (g : SL3F2) (j : Fin 2), P = (Q3 (ZMod 2) j).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨hpar, hne, hmax⟩ := hP
  obtain ⟨-, S₁, hS₁, hN⟩ := hpar
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := 3) (by norm_num)
  have hU : IsSylowTwoOf (unitriangular 3 (ZMod 2)) ⊤ := hP₀ ▸ isSylowTwoOf_top_of_sylow P₀
  obtain ⟨g, hg⟩ := exists_conj_map_eq_of_isSylowTwoOf hU hS₁
  have hNS : Subgroup.normalizer (S₁ : Set SL3F2) =
      (upperTriangular 3 (ZMod 2)).map (MulAut.conj g).toMonoidHom := by
    have key := LinearFlag.normalizer_map_conj g (unitriangular 3 (ZMod 2))
    rw [normalizer_unitriangular] at key
    rw [← hg]
    exact key
  set c : SL3F2 →* SL3F2 := (MulAut.conj g).toMonoidHom with hc
  have hcsurj : Function.Surjective c := (MulAut.conj g).surjective
  set P' : Subgroup SL3F2 := P.comap c with hP'
  have hPP' : P'.map c = P := Subgroup.map_comap_eq_self_of_surjective hcsurj P
  have hUP' : unitriangular 3 (ZMod 2) ≤ P' := by
    intro x hx
    have h1 : c x ∈ S₁ := by
      rw [← hg]
      exact Subgroup.mem_map_of_mem _ hx
    exact hN ⟨Subgroup.mem_top _, Subgroup.le_normalizer h1⟩
  have hP'ne : P' ≠ ⊤ := by
    intro h
    apply hne
    rw [← hPP', h, Subgroup.map_top_of_surjective _ hcsurj]
  have hQ : ∀ j : Fin 2, P' ≤ Q3 (ZMod 2) j → ∃ (g : SL3F2) (j : Fin 2),
      P = (Q3 (ZMod 2) j).map (MulAut.conj g).toMonoidHom := by
    intro j hj
    have hPQ : P ≤ (Q3 (ZMod 2) j).map c := by
      rw [← hPP']
      exact Subgroup.map_mono hj
    have hQpar : IsParabolic2 (⊤ : Subgroup SL3F2) ((Q3 (ZMod 2) j).map c) := by
      refine ⟨le_top, S₁, hS₁, ?_⟩
      intro y hy
      rw [inf_of_le_right le_top, hNS] at hy
      exact Subgroup.map_mono (upperTriangular_le_Q3_two j) hy
    have hQne : (Q3 (ZMod 2) j).map c ≠ ⊤ := by
      intro h
      have hQtop : Q3 (ZMod 2) j = ⊤ := by
        apply Subgroup.map_injective (f := c) (MulAut.conj g).injective
        rw [h, Subgroup.map_top_of_surjective _ hcsurj]
      fin_cases j
      · exact Q3_zero_ne_top hQtop
      · exact Q3_one_ne_top hQtop
    exact ⟨g, j, (hmax _ hQpar hQne hPQ).symm⟩
  rcases contained_in_Q3 hUP' hP'ne with h | h
  · exact hQ 0 h
  · exact hQ 1 h

end Classification

section Inner

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.Family

theorem slConjugation_toGL_eq_conj (s : SL3F2) :
    CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) (Matrix.SpecialLinearGroup.toGL s) =
      MulAut.conj s := by
  ext x : 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CatalogueBHigherLinearAction.toGL_slConjugation, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem inner_of_stable {P : Subgroup SL3F2} (hP : IsMaxParabolic2 (⊤ : Subgroup SL3F2) P)
    (α : MulAut SL3F2) (hα : P.map α.toMonoidHom = P) : ∃ s : SL3F2, α = MulAut.conj s := by
  rcases aut_SL3_cases α with ⟨A, hA⟩ | ⟨A, hA⟩
  · obtain ⟨s, hs⟩ := (slEquivGL 3).surjective A
    refine ⟨s, ?_⟩
    rw [hA, ← slConjugation_toGL_eq_conj]
    have : A = Matrix.SpecialLinearGroup.toGL s := hs.symm
    rw [this]
  · exfalso
    obtain ⟨g, j, hPg⟩ := isMaxParabolic2_eq_map_Q3 hP
    have hmapα : P.map α.toMonoidHom =
        (P.map (CatalogueBGraphForm.slGraphAut 3 (ZMod 2)).toMonoidHom).map
          (CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) A).toMonoidHom := by
      rw [Subgroup.map_map, hA]
      rfl
    have h1 : FixesVec P ↔ FixesCov P := by
      calc FixesVec P
          ↔ FixesCov (P.map (CatalogueBGraphForm.slGraphAut 3 (ZMod 2)).toMonoidHom) :=
            fixesVec_iff_fixesCov_map_tau P
        _ ↔ FixesCov ((P.map (CatalogueBGraphForm.slGraphAut 3 (ZMod 2)).toMonoidHom).map
              (CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) A).toMonoidHom) :=
            (fixesCov_map_slConj A _).symm
        _ ↔ FixesCov (P.map α.toMonoidHom) := by rw [hmapα]
        _ ↔ FixesCov P := by rw [hα]
    have hconjmap : (MulAut.conj g).toMonoidHom = (CatalogueBHigherLinearAction.slConjugation 3
        (ZMod 2) (Matrix.SpecialLinearGroup.toGL g)).toMonoidHom := by
      rw [slConjugation_toGL_eq_conj]
    have h2 : FixesVec P ↔ FixesVec (Q3 (ZMod 2) j) := by
      rw [hPg, hconjmap]
      exact fixesVec_map_slConj _ _
    have h3 : FixesCov P ↔ FixesCov (Q3 (ZMod 2) j) := by
      rw [hPg, hconjmap]
      exact fixesCov_map_slConj _ _
    have h4 : FixesVec (Q3 (ZMod 2) j) ↔ FixesCov (Q3 (ZMod 2) j) := h2.symm.trans (h1.trans h3)
    fin_cases j
    · exact not_fixesCov_Q3_zero (h4.mp fixesVec_Q3_zero)
    · exact not_fixesVec_Q3_one (h4.mpr fixesCov_Q3_one)

end Inner

end CFSG.Quasithin

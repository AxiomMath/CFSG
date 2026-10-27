module

public import CFSG.Quasithin.Vol2.Ch11SecOE8L
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualLin

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

namespace L3T

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Fin257.L3
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L

variable {F : Type} [Field F] [CharP F 2]

theorem map_Q3_zero_le :
    (Q3 F 0).map (proj 3 F) ≤
      Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  have key : ∀ g ∈ Q3 F 0, ∀ v ∈ (V1 : Subgroup (projectiveSL 3 F)),
      proj 3 F g * v * (proj 3 F g)⁻¹ ∈ (V1 : Subgroup (projectiveSL 3 F)) := by
    intro g hg v hv
    obtain ⟨a, c, rfl⟩ := mem_V1.mp hv
    have hg' : g⁻¹ ∈ Q3 F 0 := inv_mem hg
    have g10 := stabilizer_entries (k := 1) (l := 0) hg (by norm_num) (by norm_num)
    have g20 := stabilizer_entries (k := 2) (l := 0) hg (by norm_num) (by norm_num)
    have h10 := stabilizer_entries (k := 1) (l := 0) hg' (by norm_num) (by norm_num)
    have h20 := stabilizer_entries (k := 2) (l := 0) hg' (by norm_num) (by norm_num)
    have hp : proj 3 F g * (xP a * wP c) * (proj 3 F g)⁻¹ =
        proj 3 F (g * (xMat a * wMat c) * g⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv]
      rfl
    have hgh : (g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hN : ((xMat a * wMat c : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = 1 + !![0, a, c; 0, 0, 0; 0, 0, 0] := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      change xM a * wM c = _
      ext i j
      fin_cases i <;> fin_cases j <;> simp [xM, wM, Matrix.mul_apply, Fin.sum_univ_three]
    have hM : ((g * (xMat a * wMat c) * g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = 1 + (g : Matrix (Fin 3) (Fin 3) F) *
          !![0, a, c; 0, 0, 0; 0, 0, 0] *
          ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hN,
        Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hgh]
    rw [hp]
    generalize ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = H
      at h10 h20 hM
    refine proj_mem_V1_of_entries ?_ ?_ ?_ ?_ ?_ ?_ <;> rw [hM] <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, g10, g20, h10, h20]
  rintro _ ⟨g, hg, rfl⟩
  refine mem_normalizer_of_conj _ (key g hg) fun v hv => ?_
  have := key g⁻¹ (inv_mem hg) v hv
  rwa [map_inv, inv_inv] at this

theorem map_Q3_one_le :
    (Q3 F 1).map (proj 3 F) ≤
      Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  have key : ∀ g ∈ Q3 F 1, ∀ v ∈ (V2 : Subgroup (projectiveSL 3 F)),
      proj 3 F g * v * (proj 3 F g)⁻¹ ∈ (V2 : Subgroup (projectiveSL 3 F)) := by
    intro g hg v hv
    obtain ⟨b, c, rfl⟩ := mem_V2.mp hv
    have hg' : g⁻¹ ∈ Q3 F 1 := inv_mem hg
    have g20 := stabilizer_entries (k := 2) (l := 0) hg (by norm_num) (by norm_num)
    have g21 := stabilizer_entries (k := 2) (l := 1) hg (by norm_num) (by norm_num)
    have h20 := stabilizer_entries (k := 2) (l := 0) hg' (by norm_num) (by norm_num)
    have h21 := stabilizer_entries (k := 2) (l := 1) hg' (by norm_num) (by norm_num)
    have hp : proj 3 F g * (yP b * wP c) * (proj 3 F g)⁻¹ =
        proj 3 F (g * (yMat b * wMat c) * g⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv]
      rfl
    have hgh : (g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hN : ((yMat b * wMat c : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = 1 + !![0, 0, c; 0, 0, b; 0, 0, 0] := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      change yM b * wM c = _
      ext i j
      fin_cases i <;> fin_cases j <;> simp [yM, wM, Matrix.mul_apply, Fin.sum_univ_three]
    have hM : ((g * (yMat b * wMat c) * g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = 1 + (g : Matrix (Fin 3) (Fin 3) F) *
          !![0, 0, c; 0, 0, b; 0, 0, 0] *
          ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hN,
        Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hgh]
    rw [hp]
    generalize ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = H
      at h20 h21 hM
    refine proj_mem_V2_of_entries ?_ ?_ ?_ ?_ ?_ ?_ <;> rw [hM] <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, g20, g21, h20, h21]
  rintro _ ⟨g, hg, rfl⟩
  refine mem_normalizer_of_conj _ (key g hg) fun v hv => ?_
  have := key g⁻¹ (inv_mem hg) v hv
  rwa [map_inv, inv_inv] at this

theorem map_Q3_zero_eq [Finite F] :
    (Q3 F 0).map (proj 3 F) =
      Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  have hc : IsCoatom ((Q3 F 0).map (proj 3 F)) :=
    isCoatom_projStabilizer_flagSpace (K := F) (n := 3) (d := 1) le_rfl (by norm_num)
  exact ((hc.le_iff.mp map_Q3_zero_le).resolve_left normalizer_V1_lt_top.ne).symm

theorem map_Q3_one_eq [Finite F] :
    (Q3 F 1).map (proj 3 F) =
      Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  have hc : IsCoatom ((Q3 F 1).map (proj 3 F)) :=
    isCoatom_projStabilizer_flagSpace (K := F) (n := 3) (d := 2) (by norm_num) (by norm_num)
  exact ((hc.le_iff.mp map_Q3_one_le).resolve_left normalizer_V2_lt_top.ne).symm

theorem map_Q3_of_mem_semilinear [Finite F] {θ : MulAut (projectiveSL 3 F)}
    (hθE : θ ∈ semilinearAutGroup 3 F)
    (hθ : ∀ u ∈ projUnitriangular 3 F, θ u ∈ projUnitriangular 3 F) (j : Fin 2) :
    ((Q3 F j).map (proj 3 F)).map θ.toMonoidHom = (Q3 F j).map (proj 3 F) := by
  obtain ⟨h1, h2⟩ := map_V_of_mem_semilinear hθE hθ
  fin_cases j
  · change ((Q3 F 0).map (proj 3 F)).map θ.toMonoidHom = (Q3 F 0).map (proj 3 F)
    rw [map_Q3_zero_eq, Subgroup.map_equiv_normalizer_eq, h1]
  · change ((Q3 F 1).map (proj 3 F)).map θ.toMonoidHom = (Q3 F 1).map (proj 3 F)
    rw [map_Q3_one_eq, Subgroup.map_equiv_normalizer_eq, h2]

end L3T

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

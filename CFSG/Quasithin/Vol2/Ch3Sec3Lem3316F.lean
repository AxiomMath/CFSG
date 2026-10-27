module

public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3Block

public section

namespace CFSG.Quasithin.H13.L3316.SL3Aut

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L CFSG.ComponentClassification

variable {F : Type} [Field F] [Finite F]

theorem trace_eq_of_mem (j : Fin 2) (x : ↥(perfectCore (Q3 F j))) :
    ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).trace =
      1 + ((blk3 j x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace := by
  have hxQ : (x : SpecialLinearGroup (Fin 3) F) ∈ stabilizer (flagSpace 3 F ((j : ℕ) + 1)) :=
    perfectCore_le _ x.2
  have hdet := (x : SpecialLinearGroup (Fin 3) F).2
  have hdet2 := (blk3 j x).2
  rw [blk3_coe] at hdet2 ⊢
  fin_cases j
  · have h10 := stabilizer_entries hxQ (k := 1) (l := 0) (by simp) (by simp)
    have h20 := stabilizer_entries hxQ (k := 2) (l := 0) (by simp) (by simp)
    simp only [Matrix.det_fin_three, Matrix.det_fin_two, Matrix.trace_fin_three,
      Matrix.trace_fin_two, blkAt_apply] at hdet hdet2 ⊢
    simp at hdet2 ⊢
    rw [h10, h20] at hdet
    linear_combination hdet -
      (((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0) * hdet2
  · have h20 := stabilizer_entries hxQ (k := 2) (l := 0) (by simp) (by simp)
    have h21 := stabilizer_entries hxQ (k := 2) (l := 1) (by simp) (by simp)
    simp only [Matrix.det_fin_three, Matrix.det_fin_two, Matrix.trace_fin_three,
      Matrix.trace_fin_two, blkAt_apply] at hdet hdet2 ⊢
    simp at hdet2 ⊢
    rw [h20, h21] at hdet
    linear_combination hdet -
      (((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2) * hdet2

omit [Finite F] in
theorem trace_embSL (j : Fin 2) (B : SpecialLinearGroup (Fin 2) F) :
    ((embSL j B : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).trace =
      1 + (B : Matrix (Fin 2) (Fin 2) F).trace := by
  rw [coe_embSL]
  fin_cases j <;> simp [embMat, Matrix.trace_fin_three, Matrix.trace_fin_two] <;> ring

omit [Finite F] in
theorem trace_inv_sl2 (B : SpecialLinearGroup (Fin 2) F) :
    ((B⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace =
      (B : Matrix (Fin 2) (Fin 2) F).trace := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.trace_fin_two,
    Matrix.trace_fin_two]
  simp [add_comm]

omit [Finite F] in
theorem trace_conj_sl2 (c B : SpecialLinearGroup (Fin 2) F) :
    ((c * B * c⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace =
      (B : Matrix (Fin 2) (Fin 2) F).trace := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_mul]

omit [Finite F] in
theorem trace_map (σ : F ≃+* F) (M : Matrix (Fin 3) (Fin 3) F) :
    (M.map σ).trace = σ M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem center_fixed (hF4 : ∃ s : Finset F, s.card = 4)
    (φ : MulAut (SpecialLinearGroup (Fin 3) F)) (j : Fin 2)
    (hQ : (Q3 F j).map φ.toMonoidHom = Q3 F j) (c : SpecialLinearGroup (Fin 2) F)
    (hc : ∀ (x : ↥(perfectCore (Q3 F j))) (hx : φ x ∈ perfectCore (Q3 F j)),
      blk3 j ⟨φ x, hx⟩ = c * blk3 j x * c⁻¹) :
    ∀ z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F), φ z = z := by
  classical
  obtain ⟨A, σ, ε, hε, hφ⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl (n := 3) (K := F) le_rfl φ
  have hN : ∀ x ∈ perfectCore (Q3 F j), φ x ∈ perfectCore (Q3 F j) := by
    intro x hx
    have h1 : (perfectCore (Q3 F j)).map φ.toMonoidHom = perfectCore (Q3 F j) := by
      rw [map_perfectCore, hQ]
    rw [← h1]
    exact ⟨x, hx, rfl⟩
  have hmat : ∀ g, ((φ g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      A.val * ((((CatalogueBGraphForm.slGraphAut 3 F ^ ε) g : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F).map σ) * (A⁻¹).val := by
    intro g
    rw [hφ, MulAut.mul_apply, MulAut.mul_apply, CatalogueBHigherLinearAction.slConjugation_matrix]
    congr 2
  have htrφ : ∀ g, ((φ g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).trace =
      σ (((CatalogueBGraphForm.slGraphAut 3 F ^ ε) g : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F).trace := by
    intro g
    rw [hmat, Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul, trace_map]
  have hMtr : ∀ B : SpecialLinearGroup (Fin 2) F,
      (((CatalogueBGraphForm.slGraphAut 3 F ^ ε) (embSL j B) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F).trace = 1 + (B : Matrix (Fin 2) (Fin 2) F).trace := by
    intro B
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · rw [pow_zero, MulAut.one_apply, trace_embSL]
    · rw [pow_one, CatalogueBGraphForm.slGraphAut_matrix, Matrix.trace_transpose, ← map_inv,
        trace_embSL, trace_inv_sl2]
  have hσ : ∀ t : F, σ t = t := by
    intro t
    let B : SpecialLinearGroup (Fin 2) F := ⟨!![t, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
    have hx := embSL_mem_perfectCore hF4 j B
    have hNx := hN _ hx
    have h1 := trace_eq_of_mem j ⟨φ (embSL j B), hNx⟩
    rw [hc ⟨embSL j B, hx⟩ hNx, blk3_embSL hF4 j B, trace_conj_sl2, htrφ, hMtr] at h1
    have hB : (B : Matrix (Fin 2) (Fin 2) F).trace = t := by
      simp [B, Matrix.trace_fin_two]
    rw [hB, map_add, map_one] at h1
    exact add_left_cancel h1
  have hσ1 : σ = 1 := RingEquiv.ext hσ
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · intro z hz
    obtain ⟨r, -, hr⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).1 hz
    apply Subtype.ext
    have h1 : ((scalar (Fin 3) r).map ⇑(1 : F ≃+* F)) = scalar (Fin 3) r := by
      ext a b
      rfl
    rw [hmat, pow_zero, MulAut.one_apply, hσ1, ← hr, h1,
      ← (Matrix.scalar_commute r (fun r' => Commute.all r r') (A : Matrix (Fin 3) (Fin 3) F)).eq,
      Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  · exfalso
    rw [hσ1, map_one, mul_one, pow_one] at hφ
    set W := flagSpace 3 F ((j : ℕ) + 1) with hW
    have hφhom : φ.toMonoidHom = (CatalogueBHigherLinearAction.slConjugation 3 F A :
        SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F).comp
        (CatalogueBGraphForm.slGraphAut 3 F :
          SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F) := by
      rw [hφ]
      exact MonoidHom.ext fun g => rfl
    have h1 : (stabilizer W).map φ.toMonoidHom =
        stabilizer ((dotOrth W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F))) := by
      rw [hφhom, ← Subgroup.map_map, map_stabilizer_slGraphAut, map_stabilizer_slConjugation]
    have hQ' : (stabilizer W).map φ.toMonoidHom = stabilizer W := hQ
    rw [h1] at hQ'
    have h2 : projStabilizer ((dotOrth W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F))) =
        projStabilizer W := by
      unfold projStabilizer
      rw [hQ']
    have hdW : Module.finrank F W = (j : ℕ) + 1 := finrank_flagSpace (by omega)
    have hdW' : Module.finrank F ((dotOrth W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F))) =
        3 - ((j : ℕ) + 1) := by
      have := LinearEquiv.finrank_map_eq
        ((A : Matrix (Fin 3) (Fin 3) F).toLinearEquiv' A.invertible) (dotOrth W)
      exact this.trans (by rw [finrank_dotOrth, hdW])
    obtain ⟨p, hchar⟩ := CharP.exists F
    have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
    obtain ⟨-, hdisj, -⟩ := intrinsic_extremal_parabolics (K := F) (n := 3) p le_rfl
    fin_cases j
    · exact Set.disjoint_left.1 hdisj ⟨W, by simpa using hdW, rfl⟩ ⟨_, by simpa using hdW', h2⟩
    · exact Set.disjoint_left.1 hdisj ⟨_, by simpa using hdW', h2⟩ ⟨W, by simpa using hdW, rfl⟩
end CFSG.Quasithin.H13.L3316.SL3Aut

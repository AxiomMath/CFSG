module

public import CFSG.Quasithin.MS93.MSPGen3
public import CFSG.Quasithin.MS93.MSPLevi

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {F : Type} [Field F]

theorem entry_of_mem_P₂ {g : Sp4 F} (hg : g ∈ P₂ F) :
    mat g (.inl 1) (.inl 0) = 0 ∧ mat g (.inr 0) (.inl 0) = 0 ∧ mat g (.inr 1) (.inl 0) = 0 ∧
      mat g (.inr 0) (.inl 1) = 0 ∧ mat g (.inr 0) (.inr 1) = 0 := by
  have he : mat g *ᵥ e₁ F ∈ pt₀ F :=
    mulVec_mem_of_mem_stab hg (by rw [pt₀_eq_span]; exact Submodule.mem_span_singleton_self _)
  have hperp : g ∈ stab (perp (pt₀ F)) := stab_le_stab_perp _ hg
  have he₂ : (mat g *ᵥ e₂ F) (.inr 0) = 0 :=
    mem_perp_pt₀.1 (mulVec_mem_of_mem_stab hperp (mem_perp_pt₀.2 (by simp)))
  have hf₂ : (mat g *ᵥ f₂ F) (.inr 0) = 0 :=
    mem_perp_pt₀.1 (mulVec_mem_of_mem_stab hperp (mem_perp_pt₀.2 (by simp)))
  rw [pt₀_eq_span] at he
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 he
  have hcol : ∀ i, mat g i (.inl 0) = (c • e₁ F) i := fun i => by
    rw [mat_apply_eq, ← hc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcol]; simp
  · rw [hcol]; simp
  · rw [hcol]; simp
  · rw [mat_apply_eq]; exact he₂
  · rw [mat_apply_eq]; exact hf₂

@[expose] def levMat (g : Sp4 F) : Matrix (Fin 2) (Fin 2) F :=
  !![mat g (.inl 1) (.inl 1), mat g (.inl 1) (.inr 1); mat g (.inr 1) (.inl 1),
    mat g (.inr 1) (.inr 1)]

theorem levMat_mul {g h : Sp4 F} (hg : g ∈ P₂ F) (hh : h ∈ P₂ F) :
    levMat (g * h) = levMat g * levMat h := by
  obtain ⟨g0, g1, g2, -, -⟩ := entry_of_mem_P₂ hg
  obtain ⟨-, -, -, h3, h4⟩ := entry_of_mem_P₂ hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [levMat, mat_mul, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, g0, g2, h3,
      h4]

theorem det_levMat {g : Sp4 F} (hg : g ∈ P₂ F) : (levMat g).det = 1 := by
  obtain ⟨-, -, -, h3, h4⟩ := entry_of_mem_P₂ hg
  have h := form_mat g (e₂ F) (f₂ F)
  rw [form_apply, form_apply] at h
  simp only [← mat_apply_eq] at h
  simp [h3, h4] at h
  rw [levMat, det_fin_two_of]
  linear_combination h

theorem levMat_one : levMat (1 : Sp4 F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levMat, mat_one]

@[expose] def levQ : P₂ F →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨levMat g, det_levMat g.2⟩
  map_one' := Subtype.ext levMat_one
  map_mul' g h := Subtype.ext (levMat_mul g.2 h.2)

theorem coe_levQ (g : P₂ F) : (levQ g : Matrix (Fin 2) (Fin 2) F) = levMat g := rfl

theorem levMat_levHom₂ (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    levMat (levHom₂ M) = (M : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levMat, mat_levHom₂, iotaM]

theorem levQ_levHom₂ (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    levQ ⟨levHom₂ M, lev₂_le_P₂ (by rw [← range_levHom₂]; exact ⟨M, rfl⟩)⟩ = M :=
  Subtype.ext (levMat_levHom₂ M)

theorem levQ_eq_one_iff (g : P₂ F) :
    levQ g = 1 ↔ ∀ v ∈ perp (pt₀ F), mat (g : Sp4 F) *ᵥ v - v ∈ pt₀ F := by
  obtain ⟨g0, g1, g2, h3, h4⟩ := entry_of_mem_P₂ g.2
  constructor
  · intro h v hv
    have hM := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
      (M : Matrix (Fin 2) (Fin 2) F)) h
    simp only [coe_levQ, Matrix.SpecialLinearGroup.coe_one] at hM
    have e11 : mat (g : Sp4 F) (.inl 1) (.inl 1) = 1 := by simpa [levMat] using congrFun₂ hM 0 0
    have e12 : mat (g : Sp4 F) (.inl 1) (.inr 1) = 0 := by simpa [levMat] using congrFun₂ hM 0 1
    have e21 : mat (g : Sp4 F) (.inr 1) (.inl 1) = 0 := by simpa [levMat] using congrFun₂ hM 1 0
    have e22 : mat (g : Sp4 F) (.inr 1) (.inr 1) = 1 := by simpa [levMat] using congrFun₂ hM 1 1
    have hv0 : v (.inr 0) = 0 := mem_perp_pt₀.1 hv
    rw [pt₀_eq_span, Submodule.mem_span_singleton]
    refine ⟨(mat (g : Sp4 F) *ᵥ v) (.inl 0) - v (.inl 0), ext4 ?_ ?_ ?_ ?_⟩
    · simp
    · simp [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, g0, e11, e12, hv0]
    · simp [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, g1, h3, h4, hv0]
    · simp [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, g2, e21, e22, hv0]
  · intro h
    have he₂ := h (e₂ F) (mem_perp_pt₀.2 (by simp))
    have hf₂ := h (f₂ F) (mem_perp_pt₀.2 (by simp))
    rw [pt₀_eq_span, Submodule.mem_span_singleton] at he₂ hf₂
    obtain ⟨a, ha⟩ := he₂
    obtain ⟨b, hb⟩ := hf₂
    have ha1 := congrFun ha (.inl 1)
    have ha2 := congrFun ha (.inr 1)
    have hb1 := congrFun hb (.inl 1)
    have hb2 := congrFun hb (.inr 1)
    simp only [Pi.sub_apply, ← mat_apply_eq] at ha1 ha2 hb1 hb2
    apply Subtype.ext
    rw [coe_levQ, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [levMat] at ha1 ha2 hb1 hb2 ⊢ <;>
      first | linear_combination -ha1 | linear_combination -ha2 | linear_combination -hb1 |
        linear_combination -hb2

theorem mem_Q₂_iff_levQ {g : Sp4 F} :
    g ∈ Q₂ F ↔ ∃ hg : g ∈ P₂ F, mat g *ᵥ e₁ F = e₁ F ∧ levQ ⟨g, hg⟩ = 1 := by
  constructor
  · intro hg
    refine ⟨Q₂_le_P₂ hg, hg.1 _ (by rw [pt₀_eq_span]; exact Submodule.mem_span_singleton_self _),
      (levQ_eq_one_iff _).2 hg.2⟩
  · rintro ⟨hg, he, h1⟩
    refine ⟨fun v hv => ?_, (levQ_eq_one_iff ⟨g, hg⟩).1 h1⟩
    rw [pt₀_eq_span] at hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [mulVec_smul, he]

theorem levQ_of_mem_Q₂ {g : Sp4 F} (hg : g ∈ Q₂ F) : levQ ⟨g, Q₂_le_P₂ hg⟩ = 1 :=
  (levQ_eq_one_iff _).2 hg.2

@[expose] def torusPt (t : Fˣ) : Sp4 F :=
  ofMat (diagonal (Sum.elim ![(t : F), 1] ![((t⁻¹ : Fˣ) : F), 1]))
    (diagonal (Sum.elim ![((t⁻¹ : Fˣ) : F), 1] ![(t : F), 1]))
    (by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      rcases i with i | i <;> fin_cases i <;> simp)
    (by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      rcases i with i | i <;> fin_cases i <;> simp)
    (fun u v => by
      rw [form_apply, form_apply]
      simp only [mulVec_diagonal, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul]
      have ht : ((t⁻¹ : Fˣ) : F) * (t : F) = 1 := by simp
      linear_combination (u (.inl 0) * v (.inr 0) - u (.inr 0) * v (.inl 0)) * ht)

theorem torusPt_mulVec (t : Fˣ) (v : V4 F) :
    mat (torusPt t) *ᵥ v = ((t : F) * v (.inl 0)) • e₁ F + v (.inl 1) • e₂ F +
      (((t⁻¹ : Fˣ) : F) * v (.inr 0)) • f₁ F + v (.inr 1) • f₂ F := by
  rw [torusPt, mat_ofMat]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [mulVec_diagonal]

theorem torusPt_mem_P₂ (t : Fˣ) : torusPt t ∈ P₂ F := mem_stab_of_le fun v hv => by
  rw [pt₀_eq_span] at hv ⊢
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  refine Submodule.mem_span_singleton.2 ⟨(t : F) * c, ?_⟩
  rw [torusPt_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem levMat_of_mem_Q₁ {g : Sp4 F} (hg : g ∈ Q₁ F) :
    levMat g = !![1, mat g (.inl 1) (.inr 1); 0, 1] := by
  have h11 : mat g (.inl 1) (.inl 1) = 1 := by rw [mat_apply_eq, mulVec_of_mem_Q₁ hg]; simp
  have h21 : mat g (.inr 1) (.inl 1) = 0 := by rw [mat_apply_eq, mulVec_of_mem_Q₁ hg]; simp
  have h22 : mat g (.inr 1) (.inr 1) = 1 := by rw [mat_apply_eq, mulVec_of_mem_Q₁ hg]; simp
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levMat, h11, h21, h22]

end CFSG.Quasithin.MS93.MSP

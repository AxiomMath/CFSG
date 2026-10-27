module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45PgBase

public section

namespace CFSG.Quasithin.H13.F431.F48L3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin.H13.F431.F45.PgGeom

variable {F : Type} [Field F]

theorem mem_scalars_of_smul_pt (M : SpecialLinearGroup (Fin 3) F)
    (h : ∀ p : Pt F, proj 3 F M • p = p) : M ∈ scalars 3 F := by
  have hcol : ∀ v : V3 F, v ≠ 0 → ∃ a : F, a • v = (M : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
    intro v hv
    have h1 : slMap M (mkPt v hv).1 = (mkPt v hv).1 := congrArg Subtype.val (h (mkPt v hv))
    have h2 : (M : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ (mkPt v hv).1 := by
      rw [← h1]
      exact mem_slMap.mpr ⟨v, mem_mkPt hv, rfl⟩
    exact Submodule.mem_span_singleton.mp h2
  obtain ⟨a, ha⟩ : ∃ a : F, Matrix.mulVecLin (M : Matrix (Fin 3) (Fin 3) F) =
      a • (1 : Module.End F (V3 F)) := by
    refine LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent fun v => ?_
    by_cases hv : v = 0
    · intro hli
      exact hli.ne_zero 0 (by simp [hv])
    · rw [LinearIndependent.pair_iff' hv]
      intro hall
      obtain ⟨a, ha⟩ := hcol v hv
      exact hall a (by simpa using ha)
  have hM : (M : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) a := by
    ext i j
    have := congrArg (fun f : Module.End F (V3 F) => f (Pi.single j 1) i) ha
    simp only [mulVecLin_apply, mulVec_single_one, col_apply] at this
    rw [this]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hdet := M.2
  rw [hM, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  rw [scalars_eq_center, Matrix.SpecialLinearGroup.mem_center_iff]
  exact ⟨a, by rw [Fintype.card_fin]; exact hdet, hM.symm⟩

theorem eq_one_of_smul_pt {y : projectiveSL 3 F} (h : ∀ p : Pt F, y • p = p) : y = 1 := by
  obtain ⟨M, rfl⟩ := proj_surjective 3 F y
  exact proj_eq_one_iff.mpr (mem_scalars_of_smul_pt M h)

theorem eq_one_of_smul_ln {y : projectiveSL 3 F} (h : ∀ L : Ln F, y • L = L) : y = 1 := by
  refine eq_one_of_smul_pt fun p => ?_
  obtain ⟨L₁, L₂, h1, h2, hne⟩ := exists_second_line p
  have e1 := (inc_smul y p L₁).mpr h1
  have e2 := (inc_smul y p L₂).mpr h2
  rw [h L₁] at e1
  rw [h L₂] at e2
  exact ppAxioms.two_lns e1 h1 e2 h2 hne

end CFSG.Quasithin.H13.F431.F48L3

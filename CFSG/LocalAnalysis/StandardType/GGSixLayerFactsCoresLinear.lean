module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsPiGL

public section

namespace CFSG.StandardType

namespace LayerCores

open Matrix

variable {E : Type} [Field E] [Finite E] [CharP E 2]

omit [Finite E] in
theorem eq_one_of_mem_range_toGL {m : ℕ} {z : GL (Fin m) E}
    (hzc : ∀ y ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) E →* GL (Fin m) E).range,
      z * y = y * z) (hz2 : z ^ 2 = 1) : z = 1 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact Subsingleton.elim _ _
  have hcomm : ∀ t : TransvectionStruct (Fin m) E,
      Commute t.toMatrix (z : Matrix (Fin m) (Fin m) E) := by
    intro t
    have h1 := hzc (SpecialLinearGroup.toGL ⟨t.toMatrix, t.det⟩) ⟨_, rfl⟩
    have h3 := congrArg (fun g : GL (Fin m) E => (g : Matrix (Fin m) (Fin m) E)) h1
    simp only [Units.val_mul] at h3
    exact h3.symm
  have hsc : (z : Matrix (Fin m) (Fin m) E) ∈ Set.range (Matrix.scalar (Fin m)) :=
    Matrix.mem_range_scalar_of_commute_transvectionStruct hcomm
  have hmem : z ∈ Subgroup.center (GL (Fin m) E) :=
    GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr hsc
  rw [GeneralLinearGroup.center_eq_range_scalar] at hmem
  obtain ⟨c, rfl⟩ := hmem
  have hc2 : c ^ 2 = 1 := by
    rw [← map_pow] at hz2
    have h5 := congrArg (fun g : GL (Fin m) E => (g : Matrix (Fin m) (Fin m) E) ⟨0, hm⟩ ⟨0, hm⟩)
      hz2
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at h5
    exact Units.ext h5
  rw [LayerFacts.eq_one_of_sq_eq_one_charTwo hc2, map_one]

theorem hasCore_top_GL (m : ℕ) : HasCore (⊤ : Subgroup (GL (Fin m) E)) := by
  by_cases hg : 2 ≤ m ∧ (3 ≤ m ∨ ∃ s : Finset E, s.card = 4)
  · refine ⟨(SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) E →* GL (Fin m) E).range,
      le_top, fun u _ s hs => ?_, ⟨1, ?_⟩, Or.inr ⟨?_, fun z _ hzc hz2 =>
        eq_one_of_mem_range_toGL hzc hz2⟩⟩
    · rw [SpecialLinearGroup.range_toGL_eq_ker_det] at hs ⊢
      exact (MonoidHom.normal_ker _).conj_mem s hs u
    · rw [LayerFacts.ggDer_succ, LayerFacts.ggDer_zero, SpecialLinearGroup.range_toGL_eq_ker_det]
      exact Abelianization.commutator_subset_ker _
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective)
        (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hg.1 hg.2)
  · have : Group.IsSolvable (GL (Fin m) E) :=
      LayerFacts.isSolvable_of_not_goodBlock (E := fun _ : Unit => E) (m := fun _ => m)
        (b := ()) hg
    exact hasCore_of_isSolvable inferInstance

end LayerCores

end CFSG.StandardType

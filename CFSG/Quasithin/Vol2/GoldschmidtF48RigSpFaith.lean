module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45SpGeomBase

public section

namespace CFSG.Quasithin.H13.F431.F48Sp

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis
  CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.H13.F431.F45.SpGeom

variable {F : Type} [Field F]

section CharTwo

variable [CharP F 2]

omit [CharP F 2] in
theorem exists_scalar_of_smul_pt (y : antiSp F) (h : ∀ p : Pt F, y • p = p) :
    ∃ a : F, actLin y = a • (1 : Module.End F (W F)) := by
  refine LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent fun v => ?_
  by_cases hv : v = 0
  · intro hli
    exact hli.ne_zero 0 (by simp [hv])
  · rw [LinearIndependent.pair_iff' hv]
    intro hall
    have hfix : mapSub y (mkPt v hv).1 = (mkPt v hv).1 := congrArg Subtype.val (h (mkPt v hv))
    have hmem : actLin y v ∈ (mkPt v hv).1 := by
      rw [← hfix]
      exact Submodule.mem_map_of_mem (mem_mkPt hv)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    exact hall a ha

theorem eq_one_of_smul_pt {y : antiSp F} (h : ∀ p : Pt F, y • p = p) : y = 1 := by
  obtain ⟨a, ha⟩ := exists_scalar_of_smul_pt y h
  have hact : ∀ v, actLin y v = a • v := fun v => by
    rw [ha]
    rfl
  have hform := form_act y (ev 0) (ev 3)
  rw [hact, hact] at hform
  simp [minorForm_apply, ev_apply] at hform
  have ha1 : a = 1 := by
    have h3 : (a - 1) ^ 2 = 0 := by
      linear_combination hform + (1 - a) * (CharP.cast_eq_zero F 2)
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
  exact eq_one_of_actLin_eq fun v => by rw [hact, ha1, one_smul]

theorem eq_one_of_smul_ln {y : antiSp F} (h : ∀ L : Ln F, y • L = L) : y = 1 := by
  refine eq_one_of_smul_pt fun p => ?_
  obtain ⟨L₁, h1⟩ := exA p
  obtain ⟨L₂, h2, hne⟩ := exists_other_line p L₁ h1
  have e1 := (inc_smul y p L₁).mpr h1
  have e2 := (inc_smul y p L₂).mpr h2
  rw [h L₁] at e1
  rw [h L₂] at e2
  by_contra hyp
  exact hne (two_pts _ _ _ _ e1 h1 e2 h2 hyp).symm

end CharTwo

end CFSG.Quasithin.H13.F431.F48Sp

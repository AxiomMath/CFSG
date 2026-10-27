module

public import CFSG.Quasithin.Vol2.Ch10Reselect.ThmRA
public import CFSG.Quasithin.Vol2.Ch10Reselect.Homog
public import CFSG.Quasithin.Vol2.Ch10Reselect.ActML2

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {K : Type} [Field K]

theorem irrPlus_lineJ (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I) (hlt : L < fsuL0 T L)
    (hA : Concl326A T L I) [IsMulCommutative ↥(fsuVM T L I)] [Nontrivial K]
    (M : RModel T L I K) {w : Fin 2 → K} (hw0 : w ≠ 0)
    (hw : ∀ (γ : ↥(fsuML T L)) (p : UTilde K), p ∈ linePair K w → actML M γ p ∈ linePair K w)
    (hVR : fsuVM T L I ≤ reducedAggregate (L ⊔ T)) :
    IsIrrPlusIn (conjClosure L T) (reducedAggregate (L ⊔ T)) T (M.lineJ w) := by
  have hJ := jData_of_line hfsu hlt hA M hw0 hw
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) := L_le_normalizer_fsuUL T L I
  have hJU : M.lineJ w ≤ fsuUL T L I := UModel.lineJ_le_U M w hLU
  have hL0N : fsuL0 T L ≤ Subgroup.normalizer ((M.lineJ w : Subgroup G) : Set G) :=
    (fsuL0_le_fsuML h37 h38 hfsu hlt).trans hJ.norm
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp (not_le_normalizer_of_lt hlt)
  have hZeq : M.lineJ w ⊓ (fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) =
      M.lineJ w ⊓ Subgroup.centralizer (fsuL0 T L : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ inf_le_right
    · intro x hx
      obtain ⟨hxJ, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨hxJ, Subgroup.mem_inf.mpr ⟨hJU hxJ, hxC⟩⟩
  unfold IsIrrPlusIn
  refine ⟨(hJU.trans (fsuUL_le_fsuVM T L I)).trans hVR, UModel.lineJ_ne_bot M hw0 hLU, hL0N,
    ?_, ?_, ?_, ?_⟩
  ·
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      have hyx : y * x⁻¹ * y⁻¹ ∈ M.lineJ w :=
        (Subgroup.mem_normalizer_iff.mp (hL0N hy) x⁻¹).mp ((M.lineJ w).inv_mem hx)
      have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (M.lineJ w).mul_mem hx hyx
    · calc M.lineJ w = ⁅M.lineJ w, L⁆ := hJ.perf.symm
        _ ≤ ⁅M.lineJ w, conjClosure L T⁆ := Subgroup.commutator_mono le_rfl (le_fsuL0 T L)
  ·
    obtain ⟨j, hj, hjZ⟩ := UModel.exists_lineJ_not_mem_Z M hw0 hLU
    refine lt_of_le_of_ne inf_le_left (fun h => hjZ ?_)
    have hjC : j ∈ M.lineJ w ⊓ Subgroup.centralizer (fsuL0 T L : Set G) := by
      rw [h]
      exact hj
    exact Subgroup.mem_inf.mpr ⟨hJU hj, (Subgroup.mem_inf.mp hjC).2⟩
  ·
    intro J' h1 h2 h3
    have h1' : M.lineJ w ⊓ (fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) ≤ J' := by
      rw [hZeq]
      exact h1
    have h3' : L ≤ Subgroup.normalizer (J' : Set G) := (le_fsuL0 T L).trans h3
    rcases UModel.lineJ_irreducible M hw0 hLU h1' h2 h3' with h | h
    · exact Or.inl (h.trans hZeq)
    · exact Or.inr h
  ·
    exact irrPlus_homog h37 h38 hJ ht htn hVR
      (fun u hu h => UModel.mem_of_commutators_mem M inf_le_left hu h)

end CFSG.Quasithin.Vol2.Ch10Reselect

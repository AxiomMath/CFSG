module

public import CFSG.Quasithin.Vol2.Ch11SecOE8C

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3

open Matrix CFSG.CGT.Timmesfeld75 CFSG.LinearGroups CFSG.Quasithin
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] [CharP F 2]

abbrev piP (F : Type) [Field F] : SL(3, F) →* ProjectiveSpecialLinearGroup (Fin 3) F :=
  QuotientGroup.mk' (Subgroup.center SL(3, F))

omit [Finite F] [CharP F 2] in
theorem piP_injective_elation_zero :
    Function.Injective ((piP F).comp (elationSubgroup (pt F 0)).subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hA
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  obtain ⟨h1, -⟩ := entry_of_mem_elation A.2
  have h11 := h1 1 1 (by decide)
  have hr' : ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) r := hr.symm
  have hr1 : r = 1 := by
    have := congrFun (congrFun hr' 1) 1
    rw [h11] at this
    simpa using this.symm
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Subtype.ext
  rw [hr', hr1]
  simp

noncomputable abbrev kerU (F : Type) [Field F] [Finite F] [CharP F 2] :
    Subgroup ↥(elationSubgroup (pt F 0)) :=
  (rho.comp (Subgroup.inclusion elation_zero_le_stabM)).ker

theorem index_kerU : (kerU F).index = Nat.card F := by
  rw [Subgroup.index_ker, ← card_utri (F := F)]
  have hr : (rho.comp (Subgroup.inclusion (elation_zero_le_stabM (F := F)))).range = utri F := by
    ext g
    constructor
    · rintro ⟨A, rfl⟩
      rw [MonoidHom.comp_apply]
      have h := rho_elation_zero A.2
      rw [show (Subgroup.inclusion elation_zero_le_stabM A : ↥(stabM (F := F))) =
        ⟨A, elation_zero_le_stabM A.2⟩ from rfl, h]
      exact utriElt_mem_utri _
    · intro hg
      obtain ⟨c, rfl⟩ := mem_utri_iff.mp hg
      have hm : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈
          elationSubgroup (pt F 0) :=
        linear_elation_elementary_containment (show (0 : Fin 3) ≠ 1 by decide) c
      exact ⟨⟨_, hm⟩, rho_transvection_01 c⟩
  rw [hr]

omit [Finite F] [CharP F 2] in
theorem map_supU : (supU F).map (piP F) =
    projectiveElationSubgroup (pt F 0) ⊔ projectiveElationSubgroup (pt F 1) :=
  Subgroup.map_sup _ _ _

theorem not_isSolvable_of_le (hF4 : 4 ≤ Nat.card F) {R : Subgroup (ProjectiveSpecialLinearGroup
    (Fin 3) F)} (hR : projectiveElationSubgroup (pt F 0) ⊔ projectiveElationSubgroup (pt F 1) ≤ R) :
    ¬ Group.IsSolvable ↥R := by
  intro hs
  apply not_isSolvable_sup hF4
  have hS : (supU F).map (piP F) ≤ R := (map_supU (F := F)).le.trans hR
  have hs' : Group.IsSolvable ↥((supU F).map (piP F)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hS)
  set f : ↥(supU F) →* ↥((supU F).map (piP F)) := (piP F).subgroupMap (supU F) with hf
  have hker : Group.IsSolvable ↥f.ker := by
    refine Group.isSolvable_of_comm fun a b => Subtype.ext (Subtype.ext ?_)
    have ha : ((a : ↥(supU F)) : SL(3, F)) ∈ Subgroup.center SL(3, F) := by
      have h := MonoidHom.mem_ker.mp a.2
      have h' := congrArg Subtype.val h
      simpa [hf, QuotientGroup.eq_one_iff] using h'
    exact (Subgroup.mem_center_iff.mp ha _).symm
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [Subgroup.range_subtype])

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3

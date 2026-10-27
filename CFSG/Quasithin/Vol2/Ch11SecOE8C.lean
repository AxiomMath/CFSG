module

public import CFSG.Quasithin.Vol2.Ch11SecOE8B
public import CFSG.Quasithin.Vol2.Ch11SecBRootLiftSL2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3

open Matrix CFSG.CGT.Timmesfeld75 CFSG.LinearGroups
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] [CharP F 2]

abbrev supU (F : Type) [Field F] : Subgroup SL(3, F) :=
  elationSubgroup (pt F 0) ⊔ elationSubgroup (pt F 1)

omit [Finite F] [CharP F 2] in
theorem supU_le_stabM : supU F ≤ stabM := sup_le elation_zero_le_stabM elation_one_le_stabM

theorem map_rho_sup_eq_top : ((supU F).subgroupOf stabM).map rho = ⊤ := by
  set R := ((supU F).subgroupOf stabM).map rho with hR
  have hU : utri F ≤ R := by
    intro g hg
    obtain ⟨c, rfl⟩ := mem_utri_iff.mp hg
    have hm : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈
        elationSubgroup (pt F 0) :=
      linear_elation_elementary_containment (show (0 : Fin 3) ≠ 1 by decide) c
    exact ⟨⟨_, transvection_01_mem c⟩,
      Subgroup.mem_subgroupOf.mpr (le_sup_left (a := elationSubgroup (pt F 0)) hm),
      rho_transvection_01 c⟩
  rcases E1.RootLift.le_borel_or_eq_top hU with h | h
  · exfalso
    have hm : SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : F) ∈
        elationSubgroup (pt F 1) :=
      linear_elation_elementary_containment (show (1 : Fin 3) ≠ 0 by decide) 1
    have hmem : ltriElt (1 : F) ∈ R := by
      exact ⟨⟨_, transvection_10_mem 1⟩,
        Subgroup.mem_subgroupOf.mpr (le_sup_right (a := elationSubgroup (pt F 0)) hm),
        rho_transvection_10 1⟩
    have h10 : (ltriElt (1 : F) : SL(2, F)) 1 0 = 0 := h hmem
    rw [ltriElt_apply_10] at h10
    exact one_ne_zero h10
  · exact h

theorem not_isSolvable_sup (hF4 : 4 ≤ Nat.card F) : ¬ Group.IsSolvable ↥(supU F) := by
  intro hs
  apply E1.RootLift.not_isSolvable_SL2 hF4
  have hs' : Group.IsSolvable ↥((supU F).subgroupOf stabM) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe supU_le_stabM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe supU_le_stabM).injective
  have hs'' : Group.IsSolvable ↥(((supU F).subgroupOf stabM).map rho) :=
    Group.isSolvable_of_surjective (rho.subgroupMap_surjective _)
  rw [map_rho_sup_eq_top] at hs''
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.topEquiv (G := SL(2, F))).symm.toMonoidHom)
    (Subgroup.topEquiv (G := SL(2, F))).symm.injective

theorem entry_eq_zero_of_solvable (hF4 : 4 ≤ Nat.card F) {N : Subgroup SL(3, F)}
    (hNS : N ≤ supU F) (hSN : supU F ≤ Subgroup.normalizer (N : Set SL(3, F)))
    (hNs : Group.IsSolvable ↥N) {A : SL(3, F)} (hAN : A ∈ N)
    (hAU : A ∈ elationSubgroup (pt F 0)) : A 0 1 = 0 := by
  have : IsSimpleGroup SL(2, F) := E1.RootLift.isSimpleGroup_SL2 hF4
  have hNst : N ≤ stabM := hNS.trans supU_le_stabM
  set M := (N.subgroupOf stabM).map rho with hM
  have hMn : M.Normal := by
    refine ⟨fun m hm g => ?_⟩
    have hg : g ∈ ((supU F).subgroupOf stabM).map rho := by
      rw [map_rho_sup_eq_top]
      exact Subgroup.mem_top g
    obtain ⟨s, hs, rfl⟩ := hg
    obtain ⟨n, hn, rfl⟩ := hm
    refine ⟨s * n * s⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hs' : (s : SL(3, F)) ∈ supU F := Subgroup.mem_subgroupOf.mp hs
    have hn' : (n : SL(3, F)) ∈ N := Subgroup.mem_subgroupOf.mp hn
    exact Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp (hSN hs') _).mp hn')
  have hMs : Group.IsSolvable ↥M := by
    have h1 : Group.IsSolvable ↥(N.subgroupOf stabM) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hNst).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hNst).injective
    exact Group.isSolvable_of_surjective (rho.subgroupMap_surjective _)
  have hMb : M = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
    · exact h
    · exfalso
      rw [h] at hMs
      exact E1.RootLift.not_isSolvable_SL2 hF4
        (Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.topEquiv (G := SL(2, F))).symm.toMonoidHom)
          (Subgroup.topEquiv (G := SL(2, F))).symm.injective)
  have h1 : rho ⟨A, elation_zero_le_stabM hAU⟩ ∈ M :=
    ⟨⟨A, elation_zero_le_stabM hAU⟩, Subgroup.mem_subgroupOf.mpr hAN, rfl⟩
  rw [hMb, Subgroup.mem_bot, rho_elation_zero hAU] at h1
  have h2 := congrArg (fun g : SL(2, F) => g 0 1) h1
  simpa [utriElt_apply_01] using h2

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3

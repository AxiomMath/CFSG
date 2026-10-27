module

public import CFSG.RankThree.GF2n.Smith81.S81E7Lam
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Rep
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem e7Psi_pinnedElt' {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (c : K) :
    e7Psi K (pinnedElt .E7 β c) = e7Data_valid.xm K β c :=
  (e7Equiv (K := K)).symm_apply_eq.2 (Subtype.ext (CFSG.SeitzReduction.E8Pilot.coe_e7Isogeny_xm hβ c).symm)

theorem pinnedX_mem_rootSubgroup_E7 (α : Fin (Tag.rank .E7) → ℤ) (c : K) :
    CFSG.Blueprint.Chevalley.pinnedX .E7 K α c ∈ CFSG.Blueprint.Chevalley.rootSubgroup .E7 K α := by
  unfold CFSG.Blueprint.Chevalley.rootSubgroup
  exact Subgroup.subset_closure (Set.mem_range_self c)

theorem perpRoots_eq : EPilot.perpRoots .E7 = Perp := by
  have hn : highNode .E7 = node1 := by decide
  ext β
  rw [EPilot.mem_perpRoots_iff, perp_iff, hn]

theorem Lam_eq_map : Lam K =
    ((EPilot.perpLevi .E7 K).map (e7Psi K)).map (e7Data_valid.minGroup K).subtype := by
  apply le_antisymm
  · rw [Lam, Subgroup.closure_le]
    rintro g ⟨β, hβ, c, rfl⟩
    have hβR : IsRoot .E7 β := (perp_iff.1 hβ).1
    have hβP : β ∈ EPilot.perpRoots .E7 := by
      rw [perpRoots_eq]
      exact hβ
    have hmem : pinnedElt .E7 β c ∈ EPilot.perpLevi .E7 K :=
      EPilot.pinnedElt_mem_perpLevi hβP c
    have h1 : e7Psi K (pinnedElt .E7 β c) ∈ (EPilot.perpLevi .E7 K).map (e7Psi K) :=
      Subgroup.mem_map_of_mem (e7Psi K) hmem
    have h2 := Subgroup.mem_map_of_mem (e7Data_valid.minGroup K).subtype h1
    rw [e7Psi_pinnedElt' hβR c] at h2
    exact h2
  · obtain ⟨M, hM⟩ : ∃ M : Subgroup ↥(adjointGroup .E7 K),
        ∀ x, x ∈ M ↔ (e7Data_valid.minGroup K).subtype (e7Psi K x) ∈ Lam K :=
      ⟨((Lam K).comap (e7Data_valid.minGroup K).subtype).comap (e7Psi K), fun x => Iff.rfl⟩
    have hspan : CFSG.Blueprint.Chevalley.rootSpan .E7 K (EPilot.perpRoots .E7) ≤
        M.map (adjointGroup .E7 K).subtype := by
      unfold CFSG.Blueprint.Chevalley.rootSpan
      refine iSup₂_le fun β hβ => ?_
      unfold CFSG.Blueprint.Chevalley.rootSubgroup
      rw [Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      have hβP : β ∈ Perp := by
        rw [← perpRoots_eq]
        exact hβ
      have hβR : IsRoot .E7 β := (perp_iff.1 hβP).1
      have hMem : pinnedElt .E7 β c ∈ M := by
        rw [hM, e7Psi_pinnedElt' hβR c]
        exact xu_mem_Lam hβP c
      exact Subgroup.mem_map_of_mem (adjointGroup .E7 K).subtype hMem
    have hle : EPilot.perpLevi .E7 K ≤ M := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hspan (Subgroup.mem_subgroupOf.1 hx))
      have hxy : y = x := Subtype.ext hyx
      rw [← hxy]
      exact hy
    rintro g hg
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    exact (hM x).1 (hle hx)

theorem Jgrp_eq_map : Jgrp K =
    (((EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)).map (e7Psi K)).map
      (e7Data_valid.minGroup K).subtype := by
  apply le_antisymm
  · rw [Jgrp, Subgroup.closure_le]
    rintro g ⟨c, rfl | rfl⟩
    · have hsub : CFSG.Blueprint.Chevalley.rootSubgroup .E7 K theta ≤
          EPilot.highRootSL2 .E7 K := by
        unfold EPilot.highRootSL2
        exact le_sup_left
      have hmem : pinnedElt .E7 theta c ∈
          (EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) :=
        Subgroup.mem_subgroupOf.2 (hsub (pinnedX_mem_rootSubgroup_E7 theta c))
      have h1 := Subgroup.mem_map_of_mem (e7Psi K) hmem
      have h2 := Subgroup.mem_map_of_mem (e7Data_valid.minGroup K).subtype h1
      rw [e7Psi_pinnedElt' isRoot_theta c] at h2
      exact h2
    · have hsub : CFSG.Blueprint.Chevalley.rootSubgroup .E7 K (-theta) ≤
          EPilot.highRootSL2 .E7 K := by
        unfold EPilot.highRootSL2
        exact le_sup_right
      have hmem : pinnedElt .E7 (-theta) c ∈
          (EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) :=
        Subgroup.mem_subgroupOf.2 (hsub (pinnedX_mem_rootSubgroup_E7 (-theta) c))
      have h1 := Subgroup.mem_map_of_mem (e7Psi K) hmem
      have h2 := Subgroup.mem_map_of_mem (e7Data_valid.minGroup K).subtype h1
      rw [e7Psi_pinnedElt' (isRoot_neg isRoot_theta) c] at h2
      exact h2
  · obtain ⟨M, hM⟩ : ∃ M : Subgroup ↥(adjointGroup .E7 K),
        ∀ x, x ∈ M ↔ (e7Data_valid.minGroup K).subtype (e7Psi K x) ∈ Jgrp K :=
      ⟨((Jgrp K).comap (e7Data_valid.minGroup K).subtype).comap (e7Psi K), fun x => Iff.rfl⟩
    have hgen : ∀ α : Fin (Tag.rank .E7) → ℤ, (α = theta ∨ α = -theta) →
        CFSG.Blueprint.Chevalley.rootSubgroup .E7 K α ≤ M.map (adjointGroup .E7 K).subtype := by
      intro α hα
      unfold CFSG.Blueprint.Chevalley.rootSubgroup
      rw [Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      have hR : IsRoot .E7 α := by
        rcases hα with rfl | rfl
        · exact isRoot_theta
        · exact isRoot_neg isRoot_theta
      have hJ : e7Data_valid.xu K α c ∈ Jgrp K := by
        rcases hα with rfl | rfl
        · exact Subgroup.subset_closure ⟨c, Or.inl rfl⟩
        · exact Subgroup.subset_closure ⟨c, Or.inr rfl⟩
      have hMem : pinnedElt .E7 α c ∈ M := by
        rw [hM, e7Psi_pinnedElt' hR c]
        exact hJ
      exact Subgroup.mem_map_of_mem (adjointGroup .E7 K).subtype hMem
    have hspan : EPilot.highRootSL2 .E7 K ≤ M.map (adjointGroup .E7 K).subtype := by
      unfold EPilot.highRootSL2
      exact sup_le (hgen theta (Or.inl rfl)) (hgen (-theta) (Or.inr rfl))
    have hle : (EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) ≤ M := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hspan (Subgroup.mem_subgroupOf.1 hx))
      have hxy : y = x := Subtype.ext hyx
      rw [← hxy]
      exact hy
    rintro g hg
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    exact (hM x).1 (hle hx)

theorem isSimpleGroup_Lam : IsSimpleGroup (Lam K) := by
  have hD : IsSimpleGroup (EPilot.perpLevi .E7 K) :=
    CFSG.SeitzReduction.E7Pilot.isSimpleGroup_perpLevi_E7 (K := K)
  have hinj : Function.Injective (e7Psi K) := (e7Equiv (K := K)).symm.injective
  have e1 : ↥(EPilot.perpLevi .E7 K) ≃* ↥((EPilot.perpLevi .E7 K).map (e7Psi K)) :=
    (EPilot.perpLevi .E7 K).equivMapOfInjective (e7Psi K) hinj
  have e2 : ↥((EPilot.perpLevi .E7 K).map (e7Psi K)) ≃*
      ↥(((EPilot.perpLevi .E7 K).map (e7Psi K)).map (e7Data_valid.minGroup K).subtype) :=
    ((EPilot.perpLevi .E7 K).map (e7Psi K)).equivMapOfInjective
      (e7Data_valid.minGroup K).subtype Subtype.val_injective
  have e3 : ↥(((EPilot.perpLevi .E7 K).map (e7Psi K)).map (e7Data_valid.minGroup K).subtype) ≃*
      ↥(Lam K) :=
    MulEquiv.subgroupCongr Lam_eq_map.symm
  exact @MulEquiv.isSimpleGroup _ _ _ _ hD (e1.trans (e2.trans e3)).symm

end CFSG.RankThree.GF2n.Smith81.E7Model

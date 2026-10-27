module

public import CFSG.RankThree.GF2n.Smith81.S81KInvolRed

public section

namespace CFSG.RankThree.GF2n.Smith81.SK

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.SeitzReduction CFSG.SeitzReduction.E7Pilot CFSG.SeitzReduction.EPilot
  CFSG.RankThree.GF2n.Smith81.D6X CFSG.RankThree.GF2n.Smith81.E7X
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.GF2n.Smith81.MinuscT

section Nodes

@[expose] def levNodesD6 : List (Fin Tag.E7.rank) :=
  [(show Fin 7 from 1), (show Fin 7 from 2), (show Fin 7 from 3), (show Fin 7 from 4),
    (show Fin 7 from 5), (show Fin 7 from 6)]

theorem cascadeCheck_cascadeD6 : cascadeCheck Tag.E7 cascadeD6 7 levNodesD6 = true := by
  decide +kernel

theorem mem_levNodesD6_iff : ∀ j : Fin Tag.E7.rank, j ∈ levNodesD6 ↔ j ≠ highNode .E7 := by
  decide

theorem setOf_mem_levNodesD6 : {j | j ∈ levNodesD6} = perpNodes .E7 := by
  ext j
  exact mem_levNodesD6_iff j

theorem cascadeD6_nodup : cascadeD6.Nodup := by
  have h : (cascadeD6.map List.ofFn).Nodup := by decide +kernel
  exact h.of_map _

theorem parabolicPosRoots_levNodesD6 :
    parabolicPosRoots .E7 {j | j ∈ levNodesD6} = posPerpRoots := by
  rw [setOf_mem_levNodesD6, parabolicPosRoots, parabolicRoots_perpNodes]
  ext β
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, posPerpRoots, posPerpPred, perpRoots]
  tauto

end Nodes

section Roots


variable {K : Type} [Field K]

theorem rootSpan_posPerpRoots_le_perpRoots :
    rootSpan .E7 K posPerpRoots ≤ rootSpan .E7 K (perpRoots .E7) :=
  classDescent_rootSpan_mono (fun β hβ => ⟨hβ.1, hβ.2.2⟩)

theorem cascadeConjGroup_le_rootSpan_perpRoots :
    cascadeConjGroup .E7 K {j | j ∈ levNodesD6} ≤ rootSpan .E7 K (perpRoots .E7) := by
  rw [setOf_mem_levNodesD6]
  refine sup_le ?_ ((Subgroup.closure_le _).2 ?_)
  · rw [← parabolicRoots_perpNodes]
    exact classDescent_rootSpan_mono fun α hα => hα.1
  · rintro _ ⟨j, hj, rfl⟩
    exact sup_le (rootSubgroup_le_rootSpan_perpRoots (single_mem_perpRoots hj))
      (rootSubgroup_le_rootSpan_perpRoots (neg_single_mem_perpRoots hj))
      (weylElt_mem_rootPair j 1)

theorem cascadeD6_mem_perpRoots : ∀ σ ∈ cascadeD6, σ ∈ perpRoots .E7 := by
  intro σ hσ
  have h1 : (cascadeD6.all fun σ => RootOps.isRootB .E7 σ &&
      decide (σ (highNode .E7) = 0)) = true := by decide +kernel
  have := List.all_eq_true.1 h1 σ hσ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨RootOps.isRootB_iff.1 this.1, this.2⟩

theorem cascadeD6_pairwise_iform : cascadeD6.Pairwise fun σ σ' => iform σ σ' = 0 := by
  decide +kernel

end Roots

section Elements


variable {K : Type} [Field K]

theorem prod_xm_one_eq_tS (S : List Rt) :
    (S.map fun σ => e7Data_valid.xm K σ 1).prod = (⟨tS K S, tS_mem S⟩ : Gp K) := by
  induction S with
  | nil => exact Subtype.ext (tS_nil (K := K)).symm
  | cons β S ih =>
    rw [List.map_cons, List.prod_cons, ih]
    exact Subtype.ext (tS_cons (K := K) β S).symm

end Elements

section Transport


variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
noncomputable def psiLev : ↥(rootSpan .E7 K (perpRoots .E7)) →* Gp K :=
  (e7Psi K).comp (Subgroup.inclusion (rootSpan_le_adjointGroup' (perpRoots .E7)))

theorem psiLev_mem_LamG (x : ↥(rootSpan .E7 K (perpRoots .E7))) : psiLev K x ∈ LamG K := by
  rw [← psiD_range]
  exact ⟨⟨(Subgroup.inclusion (rootSpan_le_adjointGroup' (perpRoots .E7)) x),
    Subgroup.mem_subgroupOf.2 x.2⟩, rfl⟩

theorem psiLev_pinnedX {σ : Rt} (hσ : σ ∈ perpRoots .E7) (c : K) :
    psiLev K ⟨pinnedX .E7 K σ c, pinnedX_mem_rootSpan hσ c⟩ = e7Data_valid.xm K σ c :=
  e7Psi_pinnedElt' hσ.1 c

theorem psiLev_list_prod (L : List Rt) (hL : ∀ σ ∈ L, σ ∈ perpRoots .E7) (c : Rt → K) :
    psiLev K ⟨(L.map fun σ => pinnedX .E7 K σ (c σ)).prod,
        classDescent_list_prod_mem_rootSpan L hL c⟩ =
      (L.map fun σ => e7Data_valid.xm K σ (c σ)).prod := by
  induction L with
  | nil => exact map_one (psiLev K)
  | cons σ L ih =>
    have hσ := hL σ List.mem_cons_self
    have hL' : ∀ ρ ∈ L, ρ ∈ perpRoots .E7 := fun ρ h => hL ρ (List.mem_cons_of_mem _ h)
    have e : (⟨((σ :: L).map fun σ => pinnedX .E7 K σ (c σ)).prod,
        classDescent_list_prod_mem_rootSpan (σ :: L) hL c⟩ : ↥(rootSpan .E7 K (perpRoots .E7))) =
        ⟨pinnedX .E7 K σ (c σ), pinnedX_mem_rootSpan hσ (c σ)⟩ *
          ⟨(L.map fun σ => pinnedX .E7 K σ (c σ)).prod,
            classDescent_list_prod_mem_rootSpan L hL' c⟩ := rfl
    rw [e, map_mul, ih hL', psiLev_pinnedX hσ]
    rfl

theorem prod_pinnedX_eq_filter_cascade [CharP K 2] {casc S : List Rt} (hcnd : casc.Nodup)
    (hSnd : S.Nodup) (hS : ∀ σ ∈ S, σ ∈ casc ∧ IsRoot .E7 σ ∧ 0 < height σ)
    (hSo : S.Pairwise (fun σ σ' => iform σ σ' = 0)) (c : Rt → K) :
    (S.map fun σ => pinnedX .E7 K σ (c σ)).prod =
      ((casc.filter fun σ => decide (σ ∈ S)).map fun σ => pinnedX .E7 K σ (c σ)).prod := by
  have hperm : S.Perm (casc.filter fun σ => decide (σ ∈ S)) :=
    (List.perm_ext_iff_of_nodup hSnd (hcnd.filter _)).2 fun σ => by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => ⟨(hS σ h).1, h⟩, fun h => h.2⟩
  refine (hperm.map _).prod_eq' (List.pairwise_map.2 (hSo.imp_of_mem fun ha hb h => ?_))
  exact cascade_commute_pinnedX (Or.inr (Or.inr (Or.inl rfl))) (hS _ ha).2.1 (hS _ ha).2.2
    (hS _ hb).2.1 (hS _ hb).2.2 h _ _

theorem lamCascadeProd_holds : LamCascadeProdStatement := by
  intro K _ _ _ x hx hx2
  have hx' : x ∈ ((posPerpU K).subgroupOf (EPilot.perpLevi .E7 K)).map (psiD K) := by
    rw [psiD_map_posPerpU]
    exact hx
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hx'
  have hd2 : d * d = 1 := by
    apply psiD_injective (K := K)
    rw [map_mul, hx2, map_one]
  have hℓ : ((d : ↥(adjointGroup .E7 K)) : ModGL .E7 K) ∈ rootSpan .E7 K posPerpRoots :=
    Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hd)
  have hℓ2 : ((d : ↥(adjointGroup .E7 K)) : ModGL .E7 K) ^ 2 = 1 := by
    have := congrArg
      (fun y : ↥(EPilot.perpLevi .E7 K) => ((y : ↥(adjointGroup .E7 K)) : ModGL .E7 K)) hd2
    simpa [pow_two] using this
  obtain ⟨g, hg, S, hSnd, hS, hSo, c, hc, he⟩ := cascade_exists_conj_of_check (K := K)
    (Or.inr (Or.inr (Or.inl rfl))) cascadeD6 7 levNodesD6 cascadeCheck_cascadeD6
    ((d : ↥(adjointGroup .E7 K)) : ModGL .E7 K)
    (by rw [parabolicPosRoots_levNodesD6]; exact hℓ) hℓ2
  have hgL : g ∈ rootSpan .E7 K (perpRoots .E7) := cascadeConjGroup_le_rootSpan_perpRoots hg
  have hℓ' : ((d : ↥(adjointGroup .E7 K)) : ModGL .E7 K) ∈ rootSpan .E7 K (perpRoots .E7) :=
    rootSpan_posPerpRoots_le_perpRoots hℓ
  have hSp : ∀ σ ∈ S, σ ∈ perpRoots .E7 := fun σ hσ => by
    have := (hS σ hσ).2
    rw [parabolicPosRoots_levNodesD6] at this
    exact ⟨this.1, this.2.2⟩
  have hSr : ∀ σ ∈ S, σ ∈ cascadeD6 ∧ IsRoot .E7 σ ∧ 0 < height σ := fun σ hσ => by
    have := (hS σ hσ).2
    rw [parabolicPosRoots_levNodesD6] at this
    exact ⟨(hS σ hσ).1, this.1, this.2.1⟩
  set S' : List Rt := cascadeD6.filter fun σ => decide (σ ∈ S) with hS'
  have hS'mem : ∀ σ ∈ S', σ ∈ S := fun σ hσ => by simpa using (List.mem_filter.1 hσ).2
  have hprod : (S.map fun σ => pinnedX .E7 K σ (c σ)).prod =
      (S'.map fun σ => pinnedX .E7 K σ (c σ)).prod :=
    prod_pinnedX_eq_filter_cascade cascadeD6_nodup hSnd hSr hSo c
  refine ⟨psiLev K ⟨g, hgL⟩, psiLev_mem_LamG _, S', List.filter_sublist, c,
    fun σ hσ => hc σ (hS'mem σ hσ), ?_⟩
  have hSp' : ∀ σ ∈ S', σ ∈ perpRoots .E7 := fun σ hσ => hSp σ (hS'mem σ hσ)
  have hP : (S'.map fun σ => pinnedX .E7 K σ (c σ)).prod ∈ rootSpan .E7 K (perpRoots .E7) :=
    classDescent_list_prod_mem_rootSpan S' hSp' c
  have hconj : (⟨g, hgL⟩ : ↥(rootSpan .E7 K (perpRoots .E7))) *
      ⟨((d : ↥(adjointGroup .E7 K)) : ModGL .E7 K), hℓ'⟩ * ⟨g, hgL⟩⁻¹ = ⟨_, hP⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [he, hprod]
  have h1 := congrArg (psiLev K) hconj
  rw [map_mul, map_mul, map_inv, psiLev_list_prod S' hSp' c] at h1
  exact h1

theorem frameTorusElt_mem_rootSpan_perpRoots {σ : Rt} (hσ : σ (highNode .E7) = 0) (a : Kˣ) :
    frameTorusElt .E7 K σ a ∈ rootSpan .E7 K (perpRoots .E7) :=
  prod_torusElt_mem_rootSpan_perpRoots a (m := fun i => Tag.E7.symmetrizer i i * σ i)
    (by simp [hσ])

theorem exists_levi_torus_conj_frame_prod {F : List Rt} (hF : ∀ σ ∈ F, σ ∈ perpRoots .E7)
    (horth : F.Pairwise fun σ σ' => iform σ σ' = 0) (c : Rt → K) (hc : ∀ σ ∈ F, c σ ≠ 0) :
    ∃ h ∈ rootSpan .E7 K (perpRoots .E7),
      (∀ γ, IsRoot .E7 γ → (∀ σ ∈ F, iform σ γ = 0) → ∀ e : K,
        h * pinnedX .E7 K γ e * h⁻¹ = pinnedX .E7 K γ e) ∧
      h * (F.map fun σ => pinnedX .E7 K σ (c σ)).prod * h⁻¹ =
        (F.map fun σ => pinnedX .E7 K σ 1).prod := by
  induction F with
  | nil =>
    exact ⟨1, one_mem _, fun γ _ _ e => by rw [one_mul, inv_one, mul_one], by simp⟩
  | cons σ F ih =>
    obtain ⟨hσF, hFF⟩ := List.pairwise_cons.1 horth
    obtain ⟨h', hC', hfix', hprod'⟩ := ih (fun σ' h => hF σ' (List.mem_cons_of_mem _ h)) hFF
      fun σ' h => hc σ' (List.mem_cons_of_mem _ h)
    have hσp := hF σ List.mem_cons_self
    have hσ := hσp.1
    obtain ⟨a, ha⟩ := frameTorus_exists_zpow_eq (n := 2) (Or.inl rfl)
      (Units.mk0 (c σ) (hc σ List.mem_cons_self))⁻¹
    set A := frameTorusElt .E7 K σ a with hA
    have hAL : A ∈ rootSpan .E7 K (perpRoots .E7) :=
      frameTorusElt_mem_rootSpan_perpRoots hσp.2 a
    have hfixA : ∀ γ, IsRoot .E7 γ → iform σ γ = 0 → ∀ e : K,
        A * pinnedX .E7 K γ e * A⁻¹ = pinnedX .E7 K γ e := fun γ hγ h0 e => by
      rw [hA, frameTorusElt_conj_pinnedX _ _ hγ, h0, zpow_zero, Units.val_one, one_mul]
    refine ⟨A * h', mul_mem hAL hC', fun γ hγ hγF e => ?_, ?_⟩
    · rw [show A * h' * pinnedX .E7 K γ e * (A * h')⁻¹ =
          A * (h' * pinnedX .E7 K γ e * h'⁻¹) * A⁻¹ by group,
        hfix' γ hγ (fun σ' h => hγF σ' (List.mem_cons_of_mem _ h)) e,
        hfixA γ hγ (hγF σ List.mem_cons_self) e]
    · have hσ' : ∀ σ' ∈ F, iform σ' σ = 0 := fun σ' h => by rw [iform_comm]; exact hσF σ' h
      have h2 : iform σ σ = 2 := classD4_iform_self (Or.inr (Or.inr (Or.inl rfl))) hσ
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
        show A * h' * (pinnedX .E7 K σ (c σ) * (F.map fun σ => pinnedX .E7 K σ (c σ)).prod) *
            (A * h')⁻¹ = A * (h' * pinnedX .E7 K σ (c σ) * h'⁻¹) * A⁻¹ *
              (A * (h' * (F.map fun σ => pinnedX .E7 K σ (c σ)).prod * h'⁻¹) * A⁻¹) by group,
        hfix' σ hσ hσ' (c σ), hprod', frameTorusElt_conj_pinnedX _ _ hσ, h2, ha]
      refine congrArg₂ (· * ·) ?_ ?_
      · have e1 : (((Units.mk0 (c σ) (hc σ List.mem_cons_self))⁻¹ : Kˣ) : K) * c σ = 1 := by
          simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
          exact inv_mul_cancel₀ (hc σ List.mem_cons_self)
        rw [e1]
      · refine frameTorus_conj_list_prod_of_forall A _ fun x hx => ?_
        obtain ⟨σ', hσ'F, rfl⟩ := List.mem_map.1 hx
        exact hfixA σ' (hF σ' (List.mem_cons_of_mem _ hσ'F)).1 (hσF σ' hσ'F) 1

theorem lamTorusNormalize_holds : LamTorusNormalizeStatement := by
  intro K _ _ _ S hS c hc
  have hSp : ∀ σ ∈ S, σ ∈ perpRoots .E7 := fun σ hσ => cascadeD6_mem_perpRoots σ (hS.subset hσ)
  have hSo : S.Pairwise fun σ σ' => iform σ σ' = 0 := cascadeD6_pairwise_iform.sublist hS
  obtain ⟨h, hh, -, hprod⟩ := exists_levi_torus_conj_frame_prod hSp hSo c hc
  refine ⟨psiLev K ⟨h, hh⟩, psiLev_mem_LamG _, ?_⟩
  have hP : (S.map fun σ => pinnedX .E7 K σ (c σ)).prod ∈ rootSpan .E7 K (perpRoots .E7) :=
    classDescent_list_prod_mem_rootSpan S hSp c
  have hP1 : (S.map fun σ => pinnedX .E7 K σ ((fun _ => (1 : K)) σ)).prod ∈
      rootSpan .E7 K (perpRoots .E7) :=
    classDescent_list_prod_mem_rootSpan S hSp (fun _ => (1 : K))
  have hconj : (⟨h, hh⟩ : ↥(rootSpan .E7 K (perpRoots .E7))) * ⟨_, hP⟩ * ⟨h, hh⟩⁻¹ =
      ⟨_, hP1⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hprod
  have h1 := congrArg (psiLev K) hconj
  rw [map_mul, map_mul, map_inv, psiLev_list_prod S hSp c,
    psiLev_list_prod S hSp (fun _ => (1 : K))] at h1
  rw [h1]
  exact prod_xm_one_eq_tS S

end Transport

end CFSG.RankThree.GF2n.Smith81.SK

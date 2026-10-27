module

public import CFSG.Monster.B.TwoA.Amalgam.LocalBldClassical

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Geometry
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.RootSystem

theorem Pc_le_iSup_Qam
    (i : Fin 4) :
    Pc i ≤ ⨆ (j : Fin 4) (_ : j ∈ {j : Fin 4 | j ≠ i}), Qam j := by
  rcases E6.StdF4.fin4_cases i with rfl | rfl | rfl | rfl
  · exact unit_residue.2.2.2.2.1
  · exact plane4_residue.2.2.2.2
  · exact plane2_residue.2.2.2.2
  · exact orth_residue.2.2.2.2.1

theorem Pc_eq_iSup_Qam
    (i : Fin 4) : Pc i = ⨆ (j : Fin 4) (_ : j ≠ i), Qam j :=
  le_antisymm (Pc_le_iSup_Qam i) (iSup₂_le fun _ hj => Qam_le_Pc (Ne.symm hj))

theorem Eam_eq_iSup_Qam :
    Eam = ⨆ j, Qam j := by
  refine le_antisymm (iSup_le fun i => ?_) (iSup_le Qam_le_Eam)
  rw [Pc_eq_iSup_Qam i]
  exact iSup₂_le fun j _ => le_iSup Qam j

theorem Eam_le_parGroup_univ :
    Eam ≤ parGroup Set.univ := by
  rw [Eam_eq_iSup_Qam]
  exact iSup_le fun j => Qam_le_parGroup (Set.mem_univ j)

theorem mem_residue_univ
    (x y : Chamber) : y ∈ cosetCS.residue Set.univ x := by
  obtain ⟨g, rfl⟩ := chamberOf_surjective x
  obtain ⟨h, rfl⟩ := chamberOf_surjective y
  exact (mem_residue_chamberOf_iff Set.univ g h).mpr (Eam_le_parGroup_univ (h * g⁻¹).2)

theorem cosetCS_connected :
    cosetCS.Connected := fun x y => by
  obtain ⟨γ, hγ, -, hend⟩ := mem_residue_univ x y
  exact ⟨γ, hγ, hend⟩

theorem isResidueBuilding_base
    (i : Fin 4) :
    cosetCS.IsResidueBuilding nativeCoxeterSystem {j | j ≠ i} baseChamber := by
  rcases E6.StdF4.fin4_cases i with rfl | rfl | rfl | rfl
  · exact unit_residue.2.2.2.1
  · exact plane4_residue.2.2.2.1
  · exact plane2_residue.2.2.2.1
  · exact orth_residue.2.2.2.1

theorem isResidueBuilding_compl
    (i : Fin 4) (x : Chamber) :
    cosetCS.IsResidueBuilding nativeCoxeterSystem {j | j ≠ i} x := by
  obtain ⟨g, rfl⟩ := chamberOf_surjective x
  have h := (isResidueBuilding_base i).of_mem_typeAut (chamberMulPerm_mem_typeAut g)
  rwa [chamberMulPerm_chamberOf, one_mul] at h

theorem eq_compl_of_ncard_eq_three {J : Set (Fin 4)} (hJ : J.ncard = 3) :
    ∃ i : Fin 4, J = {j | j ≠ i} := by
  have h := Set.ncard_add_ncard_compl J
  rw [hJ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  obtain ⟨i, hi⟩ := Set.ncard_eq_one.mp (by omega : Jᶜ.ncard = 1)
  refine ⟨i, ?_⟩
  ext j
  have := congrArg (j ∈ ·) hi
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, eq_iff_iff] at this
  simp only [Set.mem_ofPred_eq]
  tauto

theorem exists_not_mem_of_ncard_eq_two {J : Set (Fin 4)} (hJ : J.ncard = 2) :
    ∃ i : Fin 4, i ∉ J := by
  by_contra h
  push Not at h
  have : J = Set.univ := Set.eq_univ_of_forall h
  rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hJ
  omega

theorem cosetCS_hres3
    {J : Set (Fin 4)} (hJ : J.ncard = 3) (x : Chamber) :
    cosetCS.IsResidueBuilding nativeCoxeterSystem J x := by
  obtain ⟨i, rfl⟩ := eq_compl_of_ncard_eq_three hJ
  exact isResidueBuilding_compl i x

theorem cosetCS_hres2
    {J : Set (Fin 4)} (hJ : J.ncard = 2) (x : Chamber) :
    cosetCS.IsResidueBuilding nativeCoxeterSystem J x := by
  obtain ⟨i, hi⟩ := exists_not_mem_of_ncard_eq_two hJ
  exact (isResidueBuilding_compl i x).mono fun j hj (e : j = i) => hi (e ▸ hj)

theorem encard_panel_base
    (j : Fin 4) :
    (cosetCS.residue {j} baseChamber).encard = if (j : ℕ) < 2 then 3 else 5 := by
  by_cases h3 : j = 3
  · rw [h3]
    exact unit_residue.2.2.2.2.2 3 (by decide)
  · exact orth_residue.2.2.2.2.2 j h3

theorem cosetCS_encard_panel
    (j : Fin 4) (x : Chamber) :
    (cosetCS.residue {j} x).encard = if (j : ℕ) < 2 then 3 else 5 := by
  obtain ⟨g, rfl⟩ := chamberOf_surjective x
  rw [← image_residue_chamberMulPerm, (chamberMulPerm g).injective.injOn.encard_image,
    encard_panel_base]

theorem cosetCS_hpanel
    (j : Fin 4) (x : Chamber) : ∃ y, y ≠ x ∧ cosetCS.adj j x y := by
  have h : 1 < (cosetCS.residue {j} x).encard := by
    rw [cosetCS_encard_panel]
    split_ifs <;> norm_num
  obtain ⟨y, hy, hne⟩ := Set.exists_ne_of_one_lt_encard h x
  exact ⟨y, hne, ChamberSystem.mem_residue_singleton.mp hy⟩

theorem nativeWeylEquiv_simple'
    (i : Fin 4) :
    nativeWeylEquiv (nativeCoxeterSystem.simple i) = (coxeterSystem .F4).simple i :=
  nativeWeylEquiv_simple i

theorem isResidueBuilding_F4
    {J : Set (Fin 4)} {x : Chamber}
    (h : cosetCS.IsResidueBuilding nativeCoxeterSystem J x) :
    chamberCS.IsResidueBuilding (coxeterSystem .F4) J x :=
  h.mapWeyl (cs' := coxeterSystem .F4) nativeWeylEquiv_simple' length_nativeWeylEquiv

theorem chamberCS_hpanel :
    ∀ (i : Fin Tag.F4.rank) (x : Chamber), ∃ y, y ≠ x ∧ chamberCS.adj i x y :=
  fun i x => cosetCS_hpanel i x

theorem chamberCS_hres2 :
    ∀ J : Set (Fin Tag.F4.rank), J.ncard = 2 → ∀ x,
    chamberCS.IsResidueBuilding (coxeterSystem .F4) J x :=
  fun J hJ x => isResidueBuilding_F4 (cosetCS_hres2 (J := J) hJ x)

theorem chamberCS_hres3 :
    ∀ J : Set (Fin Tag.F4.rank), J.ncard = 3 → ∀ x,
    chamberCS.IsResidueBuilding (coxeterSystem .F4) J x :=
  fun J hJ x => isResidueBuilding_F4 (cosetCS_hres3 (J := J) hJ x)

theorem chamberCS_connected :
    chamberCS.Connected := cosetCS_connected

theorem chamberCS_encard_panel :
    ∀ (i : Fin Tag.F4.rank) (x : Chamber),
    (chamberCS.residue {i} x).encard = if (i : ℕ) < 2 then 3 else 5 :=
  fun i x => cosetCS_encard_panel i x

theorem chamberCS_ncard_panel :
    ∀ (i : Fin Tag.F4.rank) (x : Chamber),
    (chamberCS.residue {i} x).ncard = if (i : ℕ) < 2 then 3 else 5 := fun i x => by
  have h := chamberCS_encard_panel i x
  rw [Set.ncard, h]
  split_ifs <;> simp

@[expose] def parJ
    (J : Set (Fin Tag.F4.rank)) : Subgroup Dfull := parGroup J

theorem parJ_eq
    (J : Set (Fin Tag.F4.rank)) :
    parJ J = Bam ⊔ ⨆ (j : Fin 4) (_ : j ∈ J), Qam j :=
  rfl

theorem Bam_le_parJ
    (J : Set (Fin Tag.F4.rank)) : Bam ≤ parJ J := Bam_le_parGroup J

theorem Qam_le_parJ
    {J : Set (Fin Tag.F4.rank)} {j : Fin Tag.F4.rank} (hj : j ∈ J) :
    Qam j ≤ parJ J :=
  Qam_le_parGroup hj

theorem parJ_le_Eam
    (J : Set (Fin Tag.F4.rank)) : parJ J ≤ Eam := parGroup_le_Eam J

theorem mem_residue_chamberCS_iff
    (J : Set (Fin Tag.F4.rank)) (g h : Eam) :
    chamberOf h ∈ chamberCS.residue J (chamberOf g) ↔ ((h * g⁻¹ : Eam) : Dfull) ∈ parJ J :=
  mem_residue_chamberOf_iff J g h

theorem chamberMulPerm_mem_typeAut_F4
    (g : Eam) : chamberMulPerm g ∈ chamberCS.typeAut :=
  chamberMulPerm_mem_typeAut g

theorem coxeterMatrix_F4_entries :
    (∀ i j : Fin 4, (coxeterMatrix (isFiniteType_cartan .F4)) (nativeIdx i) (nativeIdx j) =
      CoxeterMatrix.F₄ i j) ∧
    CoxeterMatrix.F₄ 0 1 = 3 ∧ CoxeterMatrix.F₄ 2 3 = 3 ∧ CoxeterMatrix.F₄ 1 2 = 4 ∧
    CoxeterMatrix.F₄ 0 2 = 2 ∧ CoxeterMatrix.F₄ 0 3 = 2 ∧ CoxeterMatrix.F₄ 1 3 = 2 := by
  refine ⟨fun i j => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [← coxeterMatrix_reindex_eq, CoxeterMatrix.reindex_apply, Equiv.symm_symm]
  rfl


theorem short_F4_chamber_system_local_buildings :
    (∀ g : Eam, chamberMulPerm g ∈ chamberCS.typeAut) ∧
    (∀ (h g : Eam), chamberMulPerm g (chamberOf h) = chamberOf (h * g)) ∧
    (∀ c d : Chamber, ∃ g : Eam, chamberMulPerm g c = d) ∧
    chamberCS.Connected ∧
    (∀ i : Fin 4, Pc i = ⨆ (j : Fin 4) (_ : j ≠ i), Qam j) ∧
    Eam = ⨆ j, Qam j ∧
    (∀ (J : Set (Fin Tag.F4.rank)) (g h : Eam),
      chamberOf h ∈ chamberCS.residue J (chamberOf g) ↔ ((h * g⁻¹ : Eam) : Dfull) ∈ parJ J) ∧
    (∀ J : Set (Fin Tag.F4.rank), parJ J = Bam ⊔ ⨆ (j : Fin 4) (_ : j ∈ J), Qam j) ∧
    (∀ J : Set (Fin Tag.F4.rank), J.ncard = 3 → ∀ x,
      chamberCS.IsResidueBuilding (coxeterSystem .F4) J x) ∧
    (∀ x : Chamber, ∃ ψ : PFlag UData → Chamber,
      Set.BijOn ψ Set.univ (chamberCS.residue {j | j ≠ (0 : Fin 4)} x) ∧
      ∀ a b (j : Fin 4), j ≠ 0 →
        (chamberCS.adj j (ψ a) (ψ b) ↔ (polarChamber UData (3 : Fin 4) 2 1).adj j a b)) ∧
    (∀ x : Chamber, ∃ ψ : PFlag OData → Chamber,
      Set.BijOn ψ Set.univ (chamberCS.residue {j | j ≠ (3 : Fin 4)} x) ∧
      ∀ a b (j : Fin 4), j ≠ 3 →
        (chamberCS.adj j (ψ a) (ψ b) ↔ (polarChamber OData (0 : Fin 4) 1 2).adj j a b)) ∧
    (∀ x : Chamber, ∃ ψ : IncFlag plane4Inc × Vsharp → Chamber,
      Set.BijOn ψ Set.univ (chamberCS.residue {j | j ≠ (1 : Fin 4)} x) ∧
      ∀ a b (j : Fin 4), j ≠ 1 →
        (chamberCS.adj j (ψ a) (ψ b) ↔ (incProduct plane4Inc Vsharp 2 3 0).adj j a b)) ∧
    (∀ x : Chamber, ∃ ψ : IncFlag plane2Inc × Five → Chamber,
      Set.BijOn ψ Set.univ (chamberCS.residue {j | j ≠ (2 : Fin 4)} x) ∧
      ∀ a b (j : Fin 4), j ≠ 2 →
        (chamberCS.adj j (ψ a) (ψ b) ↔ (incProduct plane2Inc Five 0 1 3).adj j a b)) ∧
    (∀ x : Chamber, ∃ ψ : PlaneFlag C2E6Overlap.K × Fin 3 → Chamber,
      Set.BijOn ψ Set.univ (chamberCS.residue {j | j ≠ (1 : Fin 4)} x) ∧
      ∀ a b (j : Fin 4), j ≠ 1 →
        (chamberCS.adj j (ψ a) (ψ b) ↔
          (planeProduct C2E6Overlap.K (Fin 3) (2 : Fin 4) 3 0).adj j a b)) ∧
    (∀ x : Chamber, ∃ ψ : PlaneFlag (ZMod 2) × Fin 5 → Chamber,
      Set.BijOn ψ Set.univ (chamberCS.residue {j | j ≠ (2 : Fin 4)} x) ∧
      ∀ a b (j : Fin 4), j ≠ 2 →
        (chamberCS.adj j (ψ a) (ψ b) ↔
          (planeProduct (ZMod 2) (Fin 5) (0 : Fin 4) 1 3).adj j a b)) ∧
    (∀ (i : Fin Tag.F4.rank) (x : Chamber),
      (chamberCS.residue {i} x).encard = if (i : ℕ) < 2 then 3 else 5) ∧
    (∀ (i : Fin Tag.F4.rank) (x : Chamber), ∃ y, y ≠ x ∧ chamberCS.adj i x y) ∧
    ((∀ i j : Fin 4, (coxeterMatrix (isFiniteType_cartan .F4)) (nativeIdx i) (nativeIdx j) =
      CoxeterMatrix.F₄ i j) ∧
      CoxeterMatrix.F₄ 0 1 = 3 ∧ CoxeterMatrix.F₄ 2 3 = 3 ∧ CoxeterMatrix.F₄ 1 2 = 4 ∧
      CoxeterMatrix.F₄ 0 2 = 2 ∧ CoxeterMatrix.F₄ 0 3 = 2 ∧ CoxeterMatrix.F₄ 1 3 = 2) ∧
    (∀ J : Set (Fin Tag.F4.rank), J.ncard = 2 → ∀ x,
      chamberCS.IsResidueBuilding (coxeterSystem .F4) J x) := by
  refine ⟨chamberMulPerm_mem_typeAut_F4, fun h g => rfl, fun c d => exists_chamberMul_eq c d,
    chamberCS_connected, Pc_eq_iSup_Qam, Eam_eq_iSup_Qam, mem_residue_chamberCS_iff, parJ_eq,
    chamberCS_hres3, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_,
    plane4_residue_classical, plane2_residue_classical, chamberCS_encard_panel,
    chamberCS_hpanel, coxeterMatrix_F4_entries, chamberCS_hres2⟩
  · exact exists_residue_iso unit_residue.1 (fun a b j hj => unit_residue.2.2.1 a b j hj) x
  · exact exists_residue_iso orth_residue.1 (fun a b j hj => orth_residue.2.2.1 a b j hj) x
  · exact exists_residue_iso plane4_residue.1 (fun a b j hj => plane4_residue.2.2.1 a b j hj) x
  · exact exists_residue_iso plane2_residue.1 (fun a b j hj => plane2_residue.2.2.1 a b j hj) x

end CFSG.Monster.B.TwoA.Amalgam

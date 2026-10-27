module

public import CFSG.Monster.B.TwoA.Amalgam.LocalBldProd
public import CFSG.Monster.B.TwoA.Amalgam.LocalBldOrth
public import CFSG.Monster.B.TwoA.Amalgam.Flag3

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.Monster.B.TwoA.Amalgam

open Module CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.C2E6Std

open scoped IsMulCommutative

attribute [local instance] subspaceAction

@[expose] def plane2Inc
    (p : SubspaceDim (ZMod 2) (Additive E3) 1)
    (l : SubspaceDim (ZMod 2) (Additive E3) 2) : Prop := p.1 ≤ l.1

theorem exists_plane2_line
    (p p' : SubspaceDim (ZMod 2) (Additive E3) 1) :
    ∃ l : SubspaceDim (ZMod 2) (Additive E3) 2, plane2Inc p l ∧ plane2Inc p' l := by
  have h0 := Submodule.finrank_add_le_finrank_add_finrank p.1 p'.1
  have e1 : finrank (ZMod 2) ↥p.1 = 1 := p.2
  have e2 : finrank (ZMod 2) ↥p'.1 = 1 := p'.2
  have h1 : finrank (ZMod 2) ↥(p.1 ⊔ p'.1) ≤ 2 := by omega
  have h2 : 2 ≤ finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) (Additive E3)) := by
    rw [finrank_top, finrank_additive_E3]
    norm_num
  obtain ⟨L, hL, -, hL2⟩ := exists_between_finrank le_top h1 h2
  exact ⟨⟨L, hL2⟩, le_sup_left.trans hL, le_sup_right.trans hL⟩

@[expose] def plane2Flag
    (g : Pc 2) : IncFlag plane2Inc :=
  ⟨((phiP3 g⁻¹).1 • ptE1, (phiP3 g⁻¹).1 • lnE2), by
    change ((phiP3 g⁻¹).1 • ptE1).1 ≤ ((phiP3 g⁻¹).1 • lnE2).1
    rw [subspace_smul_coe, subspace_smul_coe]
    exact Submodule.map_mono ptE1_le_lnE2⟩

@[expose] def plane2Model
    (g : Pc 2) : IncFlag plane2Inc × Five :=
  (plane2Flag g, (phiP3 g⁻¹).2 fiveC)

theorem quot_mk_eq_iff {G : Type*} [Group G] {H : Subgroup G} (g h : G) :
    ((g⁻¹ : G) : G ⧸ H) = (h⁻¹ : G) ↔ g * h⁻¹ ∈ H := by
  rw [QuotientGroup.eq, inv_inv]

theorem plane2_pt_eq_iff
    (g h : Pc 2) :
    (plane2Flag g).1.1 = (plane2Flag h).1.1 ↔ ((g * h⁻¹ : Pc 2) : Dfull) ∈ Pc 0 :=
  (mk_eq_mk_iff_pt g⁻¹ h⁻¹).symm.trans ((quot_mk_eq_iff g h).trans Subgroup.mem_subgroupOf)

theorem plane2_ln_eq_iff
    (g h : Pc 2) :
    (plane2Flag g).1.2 = (plane2Flag h).1.2 ↔ ((g * h⁻¹ : Pc 2) : Dfull) ∈ Pc 1 :=
  (mk_eq_mk_iff_ln g⁻¹ h⁻¹).symm.trans ((quot_mk_eq_iff g h).trans Subgroup.mem_subgroupOf)

theorem plane2_five_eq_iff
    (g h : Pc 2) :
    (plane2Model g).2 = (plane2Model h).2 ↔ ((g * h⁻¹ : Pc 2) : Dfull) ∈ Pc 3 :=
  (mk_eq_mk_iff_five g⁻¹ h⁻¹).symm.trans ((quot_mk_eq_iff g h).trans Subgroup.mem_subgroupOf)

theorem plane2Flag_eq_iff
    (g h : Pc 2) :
    plane2Flag g = plane2Flag h ↔
      ((g * h⁻¹ : Pc 2) : Dfull) ∈ Pc 0 ∧ ((g * h⁻¹ : Pc 2) : Dfull) ∈ Pc 1 := by
  rw [← plane2_pt_eq_iff, ← plane2_ln_eq_iff, Subtype.ext_iff, Prod.ext_iff]

theorem plane2Model_pt_eq_iff
    (g h : Pc 2) :
    (plane2Model g).1.1.1 = (plane2Model h).1.1.1 ↔ ((g * h⁻¹ : Pc 2) : Dfull) ∈ Pc 0 :=
  plane2_pt_eq_iff g h

theorem plane2Model_ln_eq_iff
    (g h : Pc 2) :
    (plane2Model g).1.1.2 = (plane2Model h).1.1.2 ↔ ((g * h⁻¹ : Pc 2) : Dfull) ∈ Pc 1 :=
  plane2_ln_eq_iff g h

theorem plane2Model_fst_eq_iff
    (g h : Pc 2) :
    (plane2Model g).1 = (plane2Model h).1 ↔
      ((g * h⁻¹ : Pc 2) : Dfull) ∈ Pc 0 ∧ ((g * h⁻¹ : Pc 2) : Dfull) ∈ Pc 1 :=
  plane2Flag_eq_iff g h

theorem isFlagModel_plane2Model :
    IsFlagModel (incProduct plane2Inc Five 0 1 3) plane2Model := by
  refine ⟨fun a => ?_, fun g h => ?_, fun g h j hj => ?_⟩
  · obtain ⟨⟨⟨p, l⟩, hpl⟩, C'⟩ := a
    obtain ⟨g, h1, h2, h3⟩ := p3_flag_transitive ptE1 p lnE2 l fiveC C' ptE1_le_lnE2 hpl
    have e1 : (phiP3 g⁻¹⁻¹).1 • ptE1 = p :=
      (congrArg (fun x => (phiP3 x).1 • ptE1) (inv_inv g)).trans h1
    have e2 : (phiP3 g⁻¹⁻¹).1 • lnE2 = l :=
      (congrArg (fun x => (phiP3 x).1 • lnE2) (inv_inv g)).trans h2
    have e3 : (phiP3 g⁻¹⁻¹).2 fiveC = C' :=
      (congrArg (fun x => (phiP3 x).2 fiveC) (inv_inv g)).trans h3
    exact ⟨g⁻¹, Prod.ext (Subtype.ext (Prod.ext e1 e2)) e3⟩
  · rw [Prod.ext_iff, plane2Model_fst_eq_iff, plane2_five_eq_iff,
      mem_Bam_iff_of_mem_Pc (g * h⁻¹).2]
    constructor
    · rintro ⟨⟨h0, h1⟩, h3⟩ k hk
      rcases E6.StdF4.fin4_cases k with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact absurd rfl hk
      · exact h3
    · intro hk
      exact ⟨⟨hk 0 (by decide), hk 1 (by decide)⟩, hk 3 (by decide)⟩
  · rw [mem_Qam_iff_of_mem_Pc (g * h⁻¹).2]
    rcases E6.StdF4.fin4_cases j with rfl | rfl | rfl | rfl
    · rw [incProduct_adj_a]
      show (plane2Model g).1.1.2 = (plane2Model h).1.1.2 ∧
        (plane2Model g).2 = (plane2Model h).2 ↔ _
      rw [plane2Model_ln_eq_iff, plane2_five_eq_iff]
      constructor
      · rintro ⟨h1, h3⟩ k hk2 hk0
        rcases E6.StdF4.fin4_cases k with rfl | rfl | rfl | rfl
        · exact absurd rfl hk0
        · exact h1
        · exact absurd rfl hk2
        · exact h3
      · intro hk
        exact ⟨hk 1 (by decide) (by decide), hk 3 (by decide) (by decide)⟩
    · rw [incProduct_adj_b (by decide)]
      show (plane2Model g).1.1.1 = (plane2Model h).1.1.1 ∧
        (plane2Model g).2 = (plane2Model h).2 ↔ _
      rw [plane2Model_pt_eq_iff, plane2_five_eq_iff]
      constructor
      · rintro ⟨h0, h3⟩ k hk2 hk1
        rcases E6.StdF4.fin4_cases k with rfl | rfl | rfl | rfl
        · exact h0
        · exact absurd rfl hk1
        · exact absurd rfl hk2
        · exact h3
      · intro hk
        exact ⟨hk 0 (by decide) (by decide), hk 3 (by decide) (by decide)⟩
    · exact absurd rfl hj
    · rw [incProduct_adj_z (by decide) (by decide)]
      show (plane2Model g).1 = (plane2Model h).1 ↔ _
      rw [plane2Model_fst_eq_iff]
      constructor
      · rintro ⟨h0, h1⟩ k hk2 hk3
        rcases E6.StdF4.fin4_cases k with rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact absurd rfl hk2
        · exact absurd rfl hk3
      · intro hk
        exact ⟨hk 0 (by decide) (by decide), hk 1 (by decide) (by decide)⟩

theorem plane2_types : ∀ j : Fin 4, j ≠ 2 ↔ j = 0 ∨ j = 1 ∨ j = 3 := by decide

theorem exists_ne_five
    (t : Five) : ∃ t', t' ≠ t := by
  have : Nontrivial Five := by
    rw [← Finite.one_lt_card_iff_nontrivial, natCard_orbit_subgeom]
    norm_num
  exact exists_ne t

theorem plane2_conn
    (x : IncFlag plane2Inc × Five) :
    ∃ γ : List (Fin 4 × (IncFlag plane2Inc × Five)),
      (incProduct plane2Inc Five 0 1 3).IsGallery (plane2Model 1) γ ∧
      (∀ j ∈ galleryType γ, j ∈ {j : Fin 4 | j ≠ 2}) ∧ galleryEnd (plane2Model 1) γ = x :=
  incProduct_conn (by decide) (by decide) (by decide) plane2_types exists_plane2_line
    (plane2Model 1) x

theorem plane2_residue :
    Set.BijOn (flagChamber isFlagModel_plane2Model) Set.univ
      (cosetCS.residue {j | j ≠ (2 : Fin 4)} baseChamber) ∧
    flagChamber isFlagModel_plane2Model (plane2Model 1) = baseChamber ∧
    (∀ (a b : IncFlag plane2Inc × Five) (j : Fin 4), j ≠ 2 →
      (cosetCS.adj j (flagChamber isFlagModel_plane2Model a)
        (flagChamber isFlagModel_plane2Model b) ↔
        (incProduct plane2Inc Five 0 1 3).adj j a b)) ∧
    cosetCS.IsResidueBuilding nativeCoxeterSystem {j | j ≠ (2 : Fin 4)} baseChamber ∧
    Pc 2 ≤ ⨆ (j : Fin 4) (_ : j ∈ {j : Fin 4 | j ≠ 2}), Qam j := by
  have hplane : cosetCS.IsResidueBuilding nativeCoxeterSystem {0, 1} baseChamber :=
    orth_residue.2.2.2.1.mono (by
      intro j hj
      rcases hj with rfl | hj
      · decide
      · rw [Set.mem_singleton_iff.mp hj]
        decide)
  exact ⟨bijOn_flagChamber isFlagModel_plane2Model plane2_conn,
    flagChamber_one isFlagModel_plane2Model,
    fun a b j hj => chamberAdj_flagChamber_iff isFlagModel_plane2Model hj a b,
    isResidueBuilding_of_incProduct isFlagModel_plane2Model (by decide) (by decide) (by decide)
      plane2_types exists_plane2_line rfl rfl exists_ne_five hplane,
    Pc_le_iSup_Qam_of_flagModel isFlagModel_plane2Model plane2_conn⟩

end CFSG.Monster.B.TwoA.Amalgam

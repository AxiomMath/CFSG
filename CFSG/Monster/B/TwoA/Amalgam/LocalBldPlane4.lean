module

public import CFSG.Monster.B.TwoA.Amalgam.LocalBldProd
public import CFSG.Monster.B.TwoA.Amalgam.LocalBldUnit
public import CFSG.Monster.B.TwoA.Amalgam.Flag2
import all CFSG.Fischer.F4

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Plane
  CFSG.Monster.B.Classical.ThreePlane CFSG.Monster.B.TwoA.Unitary.LinThree CFSG.Monster.B.Geometry
  CFSG.LieType.Chevalley.C2E6Std
open scoped Pointwise

@[expose] def plane4Inc (x : PlanePoint) (S : planeLines) : Prop := x ∈ (S : Set PlanePoint)

theorem exists_projLine_pair : ∀ i i' : Fin 21, ∃ b, i ∈ projLine b ∧ i' ∈ projLine b := by
  decide +kernel

theorem exists_plane4_line (x x' : PlanePoint) :
    ∃ L : planeLines, plane4Inc x L ∧ plane4Inc x' L := by
  obtain ⟨i, rfl⟩ := Ωproj.surjective x
  obtain ⟨i', rfl⟩ := Ωproj.surjective x'
  obtain ⟨b, hb, hb'⟩ := exists_projLine_pair i i'
  exact ⟨⟨lineSet b, lineSet_mem_planeLines b⟩, Ωproj_mem_lineSet.mpr hb, Ωproj_mem_lineSet.mpr hb'⟩

@[expose] def plane4Flag
    (g : Pc 1) : IncFlag plane4Inc :=
  ⟨((piTwo g⁻¹).2 • pPt, ⟨(piTwo g⁻¹).2 • ellLine, smul_mem_planeLines _ ellLine_mem_planeLines⟩),
    Set.smul_mem_smul_set pPt_mem_ellLine⟩

@[expose] def plane4Model
    (g : Pc 1) : IncFlag plane4Inc × Vsharp :=
  (plane4Flag g, (piTwo g⁻¹).1 vX)

theorem plane4_pt_eq_iff
    (g h : Pc 1) :
    (plane4Flag g).1.1 = (plane4Flag h).1.1 ↔ ((g * h⁻¹ : Pc 1) : Dfull) ∈ Pc 2 := by
  have := snd_pt_eq_iff g⁻¹ h⁻¹
  rw [inv_inv, Subgroup.mem_subgroupOf] at this
  exact this

theorem plane4_ln_eq_iff
    (g h : Pc 1) :
    (plane4Flag g).1.2 = (plane4Flag h).1.2 ↔ ((g * h⁻¹ : Pc 1) : Dfull) ∈ Pc 3 := by
  have := snd_ln_eq_iff g⁻¹ h⁻¹
  rw [inv_inv, Subgroup.mem_subgroupOf] at this
  exact Subtype.ext_iff.trans this

theorem plane4_v_eq_iff
    (g h : Pc 1) :
    (plane4Model g).2 = (plane4Model h).2 ↔ ((g * h⁻¹ : Pc 1) : Dfull) ∈ Pc 0 := by
  have := fst_eq_iff g⁻¹ h⁻¹
  rw [inv_inv, Subgroup.mem_subgroupOf] at this
  exact this

theorem plane4Flag_eq_iff
    (g h : Pc 1) :
    plane4Flag g = plane4Flag h ↔
      ((g * h⁻¹ : Pc 1) : Dfull) ∈ Pc 2 ∧ ((g * h⁻¹ : Pc 1) : Dfull) ∈ Pc 3 := by
  rw [← plane4_pt_eq_iff, ← plane4_ln_eq_iff, Subtype.ext_iff, Prod.ext_iff]

theorem isFlagModel_plane4Model :
    IsFlagModel (incProduct plane4Inc Vsharp 2 3 0) plane4Model := by
  refine ⟨fun a => ?_, fun g h => ?_, fun g h j hj => ?_⟩
  · obtain ⟨⟨⟨x, S⟩, hx⟩, v⟩ := a
    obtain ⟨g, h1, h2, h3⟩ := exists_flag v S.2 hx
    refine ⟨g⁻¹, Prod.ext (Subtype.ext (Prod.ext ?_ (Subtype.ext ?_))) ?_⟩
    · change (piTwo g⁻¹⁻¹).2 • pPt = x
      rw [inv_inv, h2]
    · change (piTwo g⁻¹⁻¹).2 • ellLine = S
      rw [inv_inv, h3]
    · change (piTwo g⁻¹⁻¹).1 vX = v
      rw [inv_inv, h1]
  · rw [plane4Model, plane4Model, Prod.ext_iff, plane4Flag_eq_iff, show (piTwo g⁻¹).1 vX =
      (plane4Model g).2 from rfl, show (piTwo h⁻¹).1 vX = (plane4Model h).2 from rfl,
      plane4_v_eq_iff, mem_Bam_iff_of_mem_Pc (g * h⁻¹).2]
    constructor
    · rintro ⟨⟨h2, h3⟩, h0⟩ k hk
      rcases E6.StdF4.fin4_cases k with rfl | rfl | rfl | rfl
      · exact h0
      · exact absurd rfl hk
      · exact h2
      · exact h3
    · intro hk
      exact ⟨⟨hk 2 (by decide), hk 3 (by decide)⟩, hk 0 (by decide)⟩
  · rw [mem_Qam_iff_of_mem_Pc (g * h⁻¹).2]
    rcases E6.StdF4.fin4_cases j with rfl | rfl | rfl | rfl
    · rw [incProduct_adj_z (by decide) (by decide)]
      change plane4Flag g = plane4Flag h ↔ _
      rw [plane4Flag_eq_iff]
      constructor
      · rintro ⟨h2, h3⟩ k hk1 hk0
        rcases E6.StdF4.fin4_cases k with rfl | rfl | rfl | rfl
        · exact absurd rfl hk0
        · exact absurd rfl hk1
        · exact h2
        · exact h3
      · intro hk
        exact ⟨hk 2 (by decide) (by decide), hk 3 (by decide) (by decide)⟩
    · exact absurd rfl hj
    · rw [incProduct_adj_a]
      change (plane4Flag g).1.2 = (plane4Flag h).1.2 ∧ (plane4Model g).2 = (plane4Model h).2 ↔ _
      rw [plane4_ln_eq_iff, plane4_v_eq_iff]
      constructor
      · rintro ⟨h3, h0⟩ k hk1 hk2
        rcases E6.StdF4.fin4_cases k with rfl | rfl | rfl | rfl
        · exact h0
        · exact absurd rfl hk1
        · exact absurd rfl hk2
        · exact h3
      · intro hk
        exact ⟨hk 3 (by decide) (by decide), hk 0 (by decide) (by decide)⟩
    · rw [incProduct_adj_b (by decide)]
      change (plane4Flag g).1.1 = (plane4Flag h).1.1 ∧ (plane4Model g).2 = (plane4Model h).2 ↔ _
      rw [plane4_pt_eq_iff, plane4_v_eq_iff]
      constructor
      · rintro ⟨h2, h0⟩ k hk1 hk3
        rcases E6.StdF4.fin4_cases k with rfl | rfl | rfl | rfl
        · exact h0
        · exact absurd rfl hk1
        · exact h2
        · exact absurd rfl hk3
      · intro hk
        exact ⟨hk 2 (by decide) (by decide), hk 0 (by decide) (by decide)⟩

theorem plane4_types : ∀ j : Fin 4, j ≠ 1 ↔ j = 2 ∨ j = 3 ∨ j = 0 := by decide

theorem exists_ne_vsharp (t : Vsharp) : ∃ t', t' ≠ t := by
  have : Nontrivial Vsharp := by
    rw [← Finite.one_lt_card_iff_nontrivial, natCard_vsharp]
    norm_num
  exact exists_ne t

theorem plane4_conn
    (x : IncFlag plane4Inc × Vsharp) :
    ∃ γ : List (Fin 4 × (IncFlag plane4Inc × Vsharp)),
      (incProduct plane4Inc Vsharp 2 3 0).IsGallery (plane4Model 1) γ ∧
      (∀ j ∈ galleryType γ, j ∈ {j : Fin 4 | j ≠ 1}) ∧ galleryEnd (plane4Model 1) γ = x :=
  incProduct_conn (by decide) (by decide) (by decide) plane4_types exists_plane4_line
    (plane4Model 1) x

theorem plane4_residue :
    Set.BijOn (flagChamber isFlagModel_plane4Model) Set.univ
      (cosetCS.residue {j | j ≠ (1 : Fin 4)} baseChamber) ∧
    flagChamber isFlagModel_plane4Model (plane4Model 1) = baseChamber ∧
    (∀ (a b : IncFlag plane4Inc × Vsharp) (j : Fin 4), j ≠ 1 →
      (cosetCS.adj j (flagChamber isFlagModel_plane4Model a)
        (flagChamber isFlagModel_plane4Model b) ↔
        (incProduct plane4Inc Vsharp 2 3 0).adj j a b)) ∧
    cosetCS.IsResidueBuilding nativeCoxeterSystem {j | j ≠ (1 : Fin 4)} baseChamber ∧
    Pc 1 ≤ ⨆ (j : Fin 4) (_ : j ∈ {j : Fin 4 | j ≠ 1}), Qam j := by
  have hplane : cosetCS.IsResidueBuilding nativeCoxeterSystem {2, 3} baseChamber :=
    unit_residue.2.2.2.1.mono (by
      intro j hj
      rcases hj with rfl | hj
      · decide
      · rw [Set.mem_singleton_iff.mp hj]
        decide)
  exact ⟨bijOn_flagChamber isFlagModel_plane4Model plane4_conn,
    flagChamber_one isFlagModel_plane4Model,
    fun a b j hj => chamberAdj_flagChamber_iff isFlagModel_plane4Model hj a b,
    isResidueBuilding_of_incProduct isFlagModel_plane4Model (by decide) (by decide) (by decide)
      plane4_types exists_plane4_line rfl rfl exists_ne_vsharp hplane,
    Pc_le_iSup_Qam_of_flagModel isFlagModel_plane4Model plane4_conn⟩

end CFSG.Monster.B.TwoA.Amalgam

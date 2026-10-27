module

public import CFSG.Monster.B.TwoA.Amalgam.LocalBld
public import CFSG.Monster.B.TwoA.Amalgam.LocalBldStd
public import CFSG.Monster.B.TwoA.Amalgam.Flag1

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open Module CFSG.Fischer CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.Geometry CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std

theorem uHerm_eq_hU (v w : V6) : uHerm v w = hU v w := by
  delta uHerm
  rw [hU, Fin.sum_univ_three]
  simp only [add_assoc]
  rfl

abbrev toUV (S : Submodule F4 V6) : Submodule C2E6Overlap.K UV := S

abbrev ofUV (S : Submodule C2E6Overlap.K UV) : Submodule F4 V6 := S

theorem uIso_of_le_V₃ (a : PFlag UData) {S : Submodule C2E6Overlap.K UV} (hS : S ≤ a.V₃) :
    ∀ s ∈ ofUV S, ∀ t ∈ ofUV S, hU s t = 0 := by
  intro s hs t ht
  rw [← uHerm_eq_hU]
  exact UData.pair_eq_zero_of_isTI a.V₃ a.isTI t (hS ht) s (hS hs)

@[expose] def unitModel
    (g : Pc 0) : PFlag UData where
  V₁ := toUV (actP1 g⁻¹ Rsp)
  V₂ := toUV (actP1 g⁻¹ Hsp)
  V₃ := toUV (actP1 g⁻¹ Tsp)
  finrank₁ := (uIso_Rsp.actP1 g⁻¹).1
  finrank₂ := (uIso_Hsp.actP1 g⁻¹).1
  finrank₃ := (uIso_Tsp.actP1 g⁻¹).1
  le₁₂ := actP1_mono Rsp_le_Hsp g⁻¹
  le₂₃ := actP1_mono Hsp_le_Tsp g⁻¹
  isTI v hv := (uHerm_eq_hU v v).trans ((uIso_Tsp.actP1 g⁻¹).2 v hv v hv)

theorem actP1_inv_eq_iff
    {O : Submodule F4 V6} {A : Subgroup (Pc 0)}
    (hO : ∀ x : Pc 0, actP1 x O = O ↔ x ∈ A) (g h : Pc 0) :
    actP1 g⁻¹ O = actP1 h⁻¹ O ↔
      ((g * h⁻¹ : Pc 0) : Dfull) ∈ ((A.map (Pc 0).subtype) : Set Dfull) := by
  have e : actP1 g⁻¹ O = actP1 h⁻¹ O ↔ actP1 (h * g⁻¹) O = O := by
    constructor
    · intro h'
      rw [actP1_mul, h', ← actP1_mul, mul_inv_cancel, actP1_one]
    · intro h'
      calc actP1 g⁻¹ O = actP1 h⁻¹ (actP1 (h * g⁻¹) O) := by
            rw [← actP1_mul, inv_mul_cancel_left]
        _ = actP1 h⁻¹ O := by rw [h']
  rw [e, hO, SetLike.mem_coe, Subgroup.mem_map]
  constructor
  · intro hA
    exact ⟨_, inv_mem hA, by simp⟩
  · rintro ⟨x, hx, hxe⟩
    have : x = g * h⁻¹ := Subtype.ext hxe
    rw [this] at hx
    simpa using inv_mem hx

theorem actP1_inv_eq_iff_Pc
    {O : Submodule F4 V6} {k : Fin 4}
    (hO : ∀ x : Pc 0, actP1 x O = O ↔ x ∈ (Pc k).subgroupOf (Pc 0)) (g h : Pc 0) :
    actP1 g⁻¹ O = actP1 h⁻¹ O ↔ ((g * h⁻¹ : Pc 0) : Dfull) ∈ Pc k := by
  rw [actP1_inv_eq_iff hO, SetLike.mem_coe, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxe⟩
    rw [← hxe]
    exact Subgroup.mem_subgroupOf.mp hx
  · intro hk
    exact ⟨g * h⁻¹, Subgroup.mem_subgroupOf.mpr hk, rfl⟩

theorem unitModel_eq_iff
    (g h : Pc 0) :
    unitModel g = unitModel h ↔ actP1 g⁻¹ Rsp = actP1 h⁻¹ Rsp ∧ actP1 g⁻¹ Hsp = actP1 h⁻¹ Hsp ∧
      actP1 g⁻¹ Tsp = actP1 h⁻¹ Tsp := by
  constructor
  · intro e
    exact ⟨congrArg PFlag.V₁ e, congrArg PFlag.V₂ e, congrArg PFlag.V₃ e⟩
  · rintro ⟨h1, h2, h3⟩
    exact PFlag.ext h1 h2 h3

theorem isFlagModel_unitModel :
    IsFlagModel (polarChamber UData (3 : Fin 4) 2 1) unitModel := by
  have hR := actP1_inv_eq_iff_Pc actP1_Rsp_iff
  have hH := actP1_inv_eq_iff_Pc actP1_Hsp_iff
  have hT := actP1_inv_eq_iff_Pc actP1_Tsp_iff
  refine ⟨fun a => ?_, fun g h => ?_, fun g h j hj => ?_⟩
  · obtain ⟨g, h1, h2, h3⟩ := exists_actP1_flag (R := ofUV a.V₁) (H := ofUV a.V₂) (T := ofUV a.V₃)
      ⟨a.finrank₁, uIso_of_le_V₃ a (a.le₁₂.trans a.le₂₃)⟩ ⟨a.finrank₂, uIso_of_le_V₃ a a.le₂₃⟩
      ⟨a.finrank₃, uIso_of_le_V₃ a le_rfl⟩ a.le₁₂ a.le₂₃
    refine ⟨g⁻¹, PFlag.ext ?_ ?_ ?_⟩
    · change actP1 g⁻¹⁻¹ Rsp = a.V₁
      rw [inv_inv, h1]
    · change actP1 g⁻¹⁻¹ Hsp = a.V₂
      rw [inv_inv, h2]
    · change actP1 g⁻¹⁻¹ Tsp = a.V₃
      rw [inv_inv, h3]
  · rw [unitModel_eq_iff, hR, hH, hT, mem_Bam_iff_of_mem_Pc (g * h⁻¹).2]
    constructor
    · rintro ⟨h3, h2, h1⟩ k hk
      rcases E6.StdF4.fin4_cases k with rfl | rfl | rfl | rfl
      · exact absurd rfl hk
      · exact h1
      · exact h2
      · exact h3
    · intro hk
      exact ⟨hk 3 (by decide), hk 2 (by decide), hk 1 (by decide)⟩
  · rw [mem_Qam_iff_of_mem_Pc (g * h⁻¹).2]
    rcases E6.StdF4.fin4_cases j with rfl | rfl | rfl | rfl
    · exact absurd rfl hj
    · rw [polarChamber_adj_π (by decide) (by decide)]
      change actP1 g⁻¹ Rsp = actP1 h⁻¹ Rsp ∧ actP1 g⁻¹ Hsp = actP1 h⁻¹ Hsp ↔ _
      rw [hR, hH]
      constructor
      · rintro ⟨h3, h2⟩ k hk0 hk1
        rcases E6.StdF4.fin4_cases k with rfl | rfl | rfl | rfl
        · exact absurd rfl hk0
        · exact absurd rfl hk1
        · exact h2
        · exact h3
      · intro hk
        exact ⟨hk 3 (by decide) (by decide), hk 2 (by decide) (by decide)⟩
    · rw [polarChamber_adj_l (by decide)]
      change actP1 g⁻¹ Rsp = actP1 h⁻¹ Rsp ∧ actP1 g⁻¹ Tsp = actP1 h⁻¹ Tsp ↔ _
      rw [hR, hT]
      constructor
      · rintro ⟨h3, h1⟩ k hk0 hk2
        rcases E6.StdF4.fin4_cases k with rfl | rfl | rfl | rfl
        · exact absurd rfl hk0
        · exact h1
        · exact absurd rfl hk2
        · exact h3
      · intro hk
        exact ⟨hk 3 (by decide) (by decide), hk 1 (by decide) (by decide)⟩
    · rw [polarChamber_adj_p]
      change actP1 g⁻¹ Hsp = actP1 h⁻¹ Hsp ∧ actP1 g⁻¹ Tsp = actP1 h⁻¹ Tsp ↔ _
      rw [hH, hT]
      constructor
      · rintro ⟨h2, h1⟩ k hk0 hk3
        rcases E6.StdF4.fin4_cases k with rfl | rfl | rfl | rfl
        · exact absurd rfl hk0
        · exact h1
        · exact h2
        · exact absurd rfl hk3
      · intro hk
        exact ⟨hk 2 (by decide) (by decide), hk 1 (by decide) (by decide)⟩

theorem unit_conn
    (a : PFlag UData) :
    ∃ γ : List (Fin 4 × PFlag UData),
      (polarChamber UData (3 : Fin 4) 2 1).IsGallery (unitModel 1) γ ∧
      (∀ j ∈ galleryType γ, j ∈ {j : Fin 4 | j ≠ (0 : Fin 4)}) ∧
      galleryEnd (unitModel 1) γ = a :=
  exists_unit_gallery _ a

theorem unit_residue :
    Set.BijOn (flagChamber isFlagModel_unitModel) Set.univ
      (cosetCS.residue {j | j ≠ (0 : Fin 4)} baseChamber) ∧
    flagChamber isFlagModel_unitModel (unitModel 1) = baseChamber ∧
    (∀ (a b : PFlag UData) (j : Fin 4), j ≠ 0 →
      (cosetCS.adj j (flagChamber isFlagModel_unitModel a)
        (flagChamber isFlagModel_unitModel b) ↔
        (polarChamber UData (3 : Fin 4) 2 1).adj j a b)) ∧
    cosetCS.IsResidueBuilding nativeCoxeterSystem {j | j ≠ (0 : Fin 4)} baseChamber ∧
    Pc 0 ≤ ⨆ (j : Fin 4) (_ : j ∈ {j : Fin 4 | j ≠ (0 : Fin 4)}), Qam j ∧
    ∀ j : Fin 4, j ≠ 0 →
      (cosetCS.residue {j} baseChamber).encard = if (j : ℕ) < 2 then 3 else 5 := by
  refine ⟨bijOn_flagChamber isFlagModel_unitModel unit_conn,
    flagChamber_one isFlagModel_unitModel,
    fun a b j hj => chamberAdj_flagChamber_iff isFlagModel_unitModel hj a b,
    isResidueBuilding_of_flagModel isFlagModel_unitModel isBuildingOn_unitDist
      (fun a b j _ => unitDist_adj_iff a b j) unit_conn,
    Pc_le_iSup_Qam_of_flagModel isFlagModel_unitModel unit_conn, fun j hj => ?_⟩
  rw [encard_panel_of_flagModel isFlagModel_unitModel hj]
  exact encard_unit_panel _ hj

end CFSG.Monster.B.TwoA.Amalgam

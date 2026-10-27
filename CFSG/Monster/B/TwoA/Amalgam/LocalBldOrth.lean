module

public import CFSG.Monster.B.TwoA.Amalgam.LocalBld
public import CFSG.Monster.B.TwoA.Amalgam.LocalBldStd
public import CFSG.Monster.B.TwoA.Amalgam.Flag4

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open Module CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.Geometry CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

theorem oQ_minusEquiv (v : V8) : oQ (minusEquiv v) = qForm v := by
  have h := qPoly_minusP (minusPinv.mulVec v)
  rw [Matrix.mulVec_mulVec, minusP_mul_minusPinv, Matrix.one_mulVec] at h
  rw [qForm_apply, h]
  rfl

theorem qForm_minusEquiv_symm (v : OV) : qForm (minusEquiv.symm v) = oQ v := by
  rw [← oQ_minusEquiv, LinearEquiv.apply_symm_apply]

@[expose] def toOFlag (F : Fin 3 → Submodule (ZMod 2) V8) (hF : F ∈ singularFlags qForm 3) :
    PFlag OData where
  V₁ := (F 0).map (minusEquiv : V8 →ₗ[ZMod 2] OV)
  V₂ := (F 1).map (minusEquiv : V8 →ₗ[ZMod 2] OV)
  V₃ := (F 2).map (minusEquiv : V8 →ₗ[ZMod 2] OV)
  finrank₁ := by rw [LinearEquiv.finrank_map_eq]; exact hF.1 0
  finrank₂ := by rw [LinearEquiv.finrank_map_eq]; exact hF.1 1
  finrank₃ := by rw [LinearEquiv.finrank_map_eq]; exact hF.1 2
  le₁₂ := Submodule.map_mono (hF.2.1 (by decide : (0 : Fin 3) ≤ 1))
  le₂₃ := Submodule.map_mono (hF.2.1 (by decide : (1 : Fin 3) ≤ 2))
  isTI := by
    rintro _ ⟨u, hu, rfl⟩
    change oQ (minusEquiv u) = 0
    rw [oQ_minusEquiv]
    exact hF.2.2 2 u hu

@[expose] def ofOFlag (a : PFlag OData) : Fin 3 → Submodule (ZMod 2) V8 :=
  ![a.V₁.map (minusEquiv.symm : OV →ₗ[ZMod 2] V8), a.V₂.map (minusEquiv.symm : OV →ₗ[ZMod 2] V8),
    a.V₃.map (minusEquiv.symm : OV →ₗ[ZMod 2] V8)]

theorem ofOFlag_mem (a : PFlag OData) : ofOFlag a ∈ singularFlags qForm 3 := by
  refine ⟨fun k => ?_, fun k k' hkk' => ?_, fun k v hv => ?_⟩
  · rcases E6.StdF4.fin3_cases k with rfl | rfl | rfl
    · exact (LinearEquiv.finrank_map_eq _ _).trans a.finrank₁
    · exact (LinearEquiv.finrank_map_eq _ _).trans a.finrank₂
    · exact (LinearEquiv.finrank_map_eq _ _).trans a.finrank₃
  · have h12 := Submodule.map_mono (f := (minusEquiv.symm : OV →ₗ[ZMod 2] V8)) a.le₁₂
    have h23 := Submodule.map_mono (f := (minusEquiv.symm : OV →ₗ[ZMod 2] V8)) a.le₂₃
    rcases E6.StdF4.fin3_cases k with rfl | rfl | rfl <;>
      rcases E6.StdF4.fin3_cases k' with rfl | rfl | rfl
    all_goals first
      | exact le_rfl
      | exact absurd hkk' (by decide)
      | exact h12
      | exact h23
      | exact h12.trans h23
  · have hle : ofOFlag a k ≤ a.V₃.map (minusEquiv.symm : OV →ₗ[ZMod 2] V8) := by
      have h12 := Submodule.map_mono (f := (minusEquiv.symm : OV →ₗ[ZMod 2] V8)) a.le₁₂
      have h23 := Submodule.map_mono (f := (minusEquiv.symm : OV →ₗ[ZMod 2] V8)) a.le₂₃
      rcases E6.StdF4.fin3_cases k with rfl | rfl | rfl
      · exact h12.trans h23
      · exact h23
      · exact le_rfl
    obtain ⟨w, hw, rfl⟩ := hle hv
    rw [LinearEquiv.coe_coe, qForm_minusEquiv_symm]
    exact a.isTI w hw

theorem map_minusEquiv_map_symm (U : Submodule (ZMod 2) OV) :
    (U.map (minusEquiv.symm : OV →ₗ[ZMod 2] V8)).map (minusEquiv : V8 →ₗ[ZMod 2] OV) = U := by
  ext v
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    rwa [LinearEquiv.apply_symm_apply]
  · intro hv
    exact ⟨minusEquiv.symm v, ⟨v, hv, rfl⟩, LinearEquiv.apply_symm_apply _ _⟩

theorem toOFlag_ofOFlag (a : PFlag OData) : toOFlag (ofOFlag a) (ofOFlag_mem a) = a :=
  PFlag.ext (map_minusEquiv_map_symm _) (map_minusEquiv_map_symm _) (map_minusEquiv_map_symm _)

@[expose] def rho4 :
    Pc 3 →* TauCeti.QuadraticMap.orthogonalGroup qForm := p4Proj

theorem map_rho4_mul
    (a b : Pc 3) (W : Submodule (ZMod 2) V8) :
    W.map (rho4 (a * b) : V8 →ₗ[ZMod 2] V8) =
      (W.map (rho4 b : V8 →ₗ[ZMod 2] V8)).map (rho4 a : V8 →ₗ[ZMod 2] V8) :=
  map_p4Proj_mul a b W

theorem map_rho4_one
    (W : Submodule (ZMod 2) V8) :
    W.map (rho4 1 : V8 →ₗ[ZMod 2] V8) = W :=
  map_p4Proj_one W

theorem rho4_mem_iff
    (k : Fin 3) (x : Pc 3) :
    (x : Dfull) ∈ Pc k.castSucc ↔ (flag4W k).map (rho4 x : V8 →ₗ[ZMod 2] V8) = flag4W k :=
  ⟨fun h => (mem_flag4H_iff k x).mp (Subgroup.mem_subgroupOf.mpr ⟨x.2, h⟩),
    fun h => (Subgroup.mem_subgroupOf.mp ((mem_flag4H_iff k x).mpr h)).2⟩

@[expose] def orthObj
    (g : Pc 3) (k : Fin 3) : Submodule (ZMod 2) V8 :=
  (flag4W k).map (rho4 g⁻¹ : V8 →ₗ[ZMod 2] V8)

theorem orthObj_mem
    (g : Pc 3) : orthObj g ∈ singularFlags qForm 3 := by
  refine ⟨fun k => (map_p4Proj_mem g⁻¹ (flag4W_mem k)).1, fun k k' hkk' => ?_,
    fun k => (map_p4Proj_mem g⁻¹ (flag4W_mem k)).2⟩
  exact Submodule.map_mono (flag4W_mono hkk')

@[expose] def orthModel
    (g : Pc 3) : PFlag OData := toOFlag (orthObj g) (orthObj_mem g)

theorem orthObj_eq_iff
    (k : Fin 3) (g h : Pc 3) :
    orthObj g k = orthObj h k ↔ ((g * h⁻¹ : Pc 3) : Dfull) ∈ Pc k.castSucc := by
  have e1 : ∀ x : Pc 3, ((flag4W k).map (rho4 x⁻¹ : V8 →ₗ[ZMod 2] V8)).map
      (rho4 h : V8 →ₗ[ZMod 2] V8) = (flag4W k).map (rho4 (h * x⁻¹) : V8 →ₗ[ZMod 2] V8) :=
    fun x => (map_rho4_mul h x⁻¹ _).symm
  have hinj : Function.Injective (Submodule.map (rho4 h : V8 →ₗ[ZMod 2] V8)) :=
    Submodule.map_injective_of_injective (rho4 h : V8 ≃ₗ[ZMod 2] V8).injective
  rw [orthObj, orthObj, ← hinj.eq_iff, e1, e1, mul_inv_cancel, map_rho4_one, ← rho4_mem_iff]
  exact ⟨fun h' => by simpa using inv_mem h', fun h' => by simpa using inv_mem h'⟩

theorem orthModel_V₁
    (g : Pc 3) :
    (orthModel g).V₁ = (orthObj g 0).map (minusEquiv : V8 →ₗ[ZMod 2] OV) := rfl

theorem orthModel_V₂
    (g : Pc 3) :
    (orthModel g).V₂ = (orthObj g 1).map (minusEquiv : V8 →ₗ[ZMod 2] OV) := rfl

theorem orthModel_V₃
    (g : Pc 3) :
    (orthModel g).V₃ = (orthObj g 2).map (minusEquiv : V8 →ₗ[ZMod 2] OV) := rfl

theorem map_minusEquiv_inj {U U' : Submodule (ZMod 2) V8} :
    U.map (minusEquiv : V8 →ₗ[ZMod 2] OV) = U'.map (minusEquiv : V8 →ₗ[ZMod 2] OV) ↔ U = U' :=
  (Submodule.map_injective_of_injective minusEquiv.injective).eq_iff

theorem orthModel_eq_iff_obj
    (g h : Pc 3) :
    orthModel g = orthModel h ↔ ∀ k : Fin 3, orthObj g k = orthObj h k := by
  constructor
  · intro e k
    rcases E6.StdF4.fin3_cases k with rfl | rfl | rfl
    · exact map_minusEquiv_inj.mp (congrArg PFlag.V₁ e)
    · exact map_minusEquiv_inj.mp (congrArg PFlag.V₂ e)
    · exact map_minusEquiv_inj.mp (congrArg PFlag.V₃ e)
  · intro e
    exact PFlag.ext (by rw [orthModel_V₁, orthModel_V₁, e 0])
      (by rw [orthModel_V₂, orthModel_V₂, e 1])
      (by rw [orthModel_V₃, orthModel_V₃, e 2])

theorem isFlagModel_orthModel :
    IsFlagModel (polarChamber OData (0 : Fin 4) 1 2) orthModel := by
  refine ⟨fun a => ?_, fun g h => ?_, fun g h j hj => ?_⟩
  · obtain ⟨g, hg⟩ := p4_flag_transitive flag4W_mem_singularFlags (ofOFlag_mem a)
    let g' : Pc 3 := ⟨g.1, g.2⟩
    refine ⟨g'⁻¹, ?_⟩
    rw [← toOFlag_ofOFlag a]
    unfold orthModel
    congr 1
    funext k
    rw [orthObj, inv_inv]
    exact hg k
  · rw [orthModel_eq_iff_obj, mem_Bam_iff_of_mem_Pc (g * h⁻¹).2]
    simp only [orthObj_eq_iff]
    constructor
    · intro hk k hk3
      rcases E6.StdF4.fin4_cases k with rfl | rfl | rfl | rfl
      · exact hk 0
      · exact hk 1
      · exact hk 2
      · exact absurd rfl hk3
    · intro hk k
      exact hk _ (by rcases E6.StdF4.fin3_cases k with rfl | rfl | rfl <;> decide)
  · rw [mem_Qam_iff_of_mem_Pc (g * h⁻¹).2]
    have key : ∀ k : Fin 3, ((g * h⁻¹ : Pc 3) : Dfull) ∈ Pc k.castSucc ↔
        orthObj g k = orthObj h k := fun k => (orthObj_eq_iff k g h).symm
    rcases E6.StdF4.fin4_cases j with rfl | rfl | rfl | rfl
    · rw [polarChamber_adj_p]
      simp only [orthModel_V₂, orthModel_V₃, map_minusEquiv_inj]
      constructor
      · rintro ⟨h1, h2⟩ k hk3 hk0
        rcases E6.StdF4.fin4_cases k with rfl | rfl | rfl | rfl
        · exact absurd rfl hk0
        · exact (key 1).mpr h1
        · exact (key 2).mpr h2
        · exact absurd rfl hk3
      · intro hk
        exact ⟨(key 1).mp (hk 1 (by decide) (by decide)), (key 2).mp (hk 2 (by decide) (by decide))⟩
    · rw [polarChamber_adj_l (by decide)]
      simp only [orthModel_V₁, orthModel_V₃, map_minusEquiv_inj]
      constructor
      · rintro ⟨h1, h2⟩ k hk3 hk1
        rcases E6.StdF4.fin4_cases k with rfl | rfl | rfl | rfl
        · exact (key 0).mpr h1
        · exact absurd rfl hk1
        · exact (key 2).mpr h2
        · exact absurd rfl hk3
      · intro hk
        exact ⟨(key 0).mp (hk 0 (by decide) (by decide)), (key 2).mp (hk 2 (by decide) (by decide))⟩
    · rw [polarChamber_adj_π (by decide) (by decide)]
      simp only [orthModel_V₁, orthModel_V₂, map_minusEquiv_inj]
      constructor
      · rintro ⟨h1, h2⟩ k hk3 hk2
        rcases E6.StdF4.fin4_cases k with rfl | rfl | rfl | rfl
        · exact (key 0).mpr h1
        · exact (key 1).mpr h2
        · exact absurd rfl hk2
        · exact absurd rfl hk3
      · intro hk
        exact ⟨(key 0).mp (hk 0 (by decide) (by decide)), (key 1).mp (hk 1 (by decide) (by decide))⟩
    · exact absurd rfl hj

theorem orth_conn
    (a : PFlag OData) :
    ∃ γ : List (Fin 4 × PFlag OData),
      (polarChamber OData (0 : Fin 4) 1 2).IsGallery (orthModel 1) γ ∧
      (∀ j ∈ galleryType γ, j ∈ {j : Fin 4 | j ≠ (3 : Fin 4)}) ∧
      galleryEnd (orthModel 1) γ = a :=
  exists_orth_gallery _ a

theorem orth_residue :
    Set.BijOn (flagChamber isFlagModel_orthModel) Set.univ
      (cosetCS.residue {j | j ≠ (3 : Fin 4)} baseChamber) ∧
    flagChamber isFlagModel_orthModel (orthModel 1) = baseChamber ∧
    (∀ (a b : PFlag OData) (j : Fin 4), j ≠ 3 →
      (cosetCS.adj j (flagChamber isFlagModel_orthModel a)
        (flagChamber isFlagModel_orthModel b) ↔
        (polarChamber OData (0 : Fin 4) 1 2).adj j a b)) ∧
    cosetCS.IsResidueBuilding nativeCoxeterSystem {j | j ≠ (3 : Fin 4)} baseChamber ∧
    Pc 3 ≤ ⨆ (j : Fin 4) (_ : j ∈ {j : Fin 4 | j ≠ (3 : Fin 4)}), Qam j ∧
    ∀ j : Fin 4, j ≠ 3 →
      (cosetCS.residue {j} baseChamber).encard = if (j : ℕ) < 2 then 3 else 5 := by
  refine ⟨bijOn_flagChamber isFlagModel_orthModel orth_conn,
    flagChamber_one isFlagModel_orthModel,
    fun a b j hj => chamberAdj_flagChamber_iff isFlagModel_orthModel hj a b,
    isResidueBuilding_of_flagModel isFlagModel_orthModel isBuildingOn_orthDist
      (fun a b j _ => orthDist_adj_iff a b j) orth_conn,
    Pc_le_iSup_Qam_of_flagModel isFlagModel_orthModel orth_conn, fun j hj => ?_⟩
  rw [encard_panel_of_flagModel isFlagModel_orthModel hj]
  exact encard_orth_panel _ hj

end CFSG.Monster.B.TwoA.Amalgam

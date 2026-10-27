module

public import CFSG.Monster.B.Geometry.UnitaryModel
public import CFSG.Monster.B.Geometry.QuadrangleModel
public import CFSG.LieType.Chevalley.C2E6UnitaryFourIncidence

public section

namespace CFSG.Monster.B.Geometry

open Module CoxeterSystem CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding
open CFSG.LieType.Chevalley.C2E6Overlap (K bar QVertex)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem uHerm_single_zero (v : UV) : uHerm v (Pi.single 0 1) = v 3 := by
  simp [uHerm, C2E6Overlap.bar_zero, C2E6Overlap.bar_one]

theorem uHerm_self_single_zero : uHerm (Pi.single 0 1) (Pi.single 0 1) = 0 := by
  rw [uHerm_single_zero]
  rfl

@[expose] def uProj : UV →ₗ[K] C2E6Overlap.V where
  toFun v := ![v 1, v 2, v 5, v 4]
  map_add' v w := by funext i; fin_cases i <;> rfl
  map_smul' c v := by funext i; fin_cases i <;> rfl

theorem uProj_apply (v : UV) : uProj v = ![v 1, v 2, v 5, v 4] := rfl

theorem uProj_single_zero : uProj (Pi.single 0 1) = 0 := by
  funext i
  fin_cases i <;> rfl

theorem herm_uProj {v w : UV} (hv : v 3 = 0) (hw : w 3 = 0) :
    C2E6Overlap.herm (uProj v) (uProj w) = uHerm v w := by
  simp only [C2E6Overlap.herm, uProj_apply, uHerm, hv, hw, C2E6Overlap.bar_zero]
  simp
  ring

theorem eq_smul_of_uProj_eq_zero {v : UV} (hv : v 3 = 0) (h : uProj v = 0) :
    v = v 0 • Pi.single 0 1 := by
  have h' : ∀ i, (![v 1, v 2, v 5, v 4] : C2E6Overlap.V) i = 0 := fun i => by
    rw [← uProj_apply, h]
    rfl
  have e1 := h' 0
  have e2 := h' 1
  have e5 := h' 2
  have e4 := h' 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at e1 e2 e5 e4
  funext i
  fin_cases i <;> simp [hv, e1, e2, e4, e5]

theorem v3_eq_zero_of_uIso {U : Submodule K UV} (hU : ∀ v ∈ U, uHerm v v = 0)
    (he : (Pi.single 0 1 : UV) ∈ U) {v : UV} (hv : v ∈ U) : v 3 = 0 := by
  rw [← uHerm_single_zero v]
  exact uHerm_eq_zero_of_isTI hU hv he

theorem single_zero_ne_zero_UV : (Pi.single 0 1 : UV) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

theorem finrank_map_uProj_add_one {U : Submodule K UV} (hU : ∀ v ∈ U, uHerm v v = 0)
    (he : (Pi.single 0 1 : UV) ∈ U) :
    finrank K (U.map uProj) + 1 = finrank K U := by
  have h := LinearMap.finrank_range_add_finrank_ker (uProj.domRestrict U)
  rw [LinearMap.range_domRestrict] at h
  have hker : LinearMap.ker (uProj.domRestrict U) = K ∙ (⟨Pi.single 0 1, he⟩ : U) := by
    ext u
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_span_singleton]
    constructor
    · intro hu
      refine ⟨(u : UV) 0, Subtype.ext ?_⟩
      rw [Submodule.coe_smul]
      exact (eq_smul_of_uProj_eq_zero (v3_eq_zero_of_uIso hU he u.2) hu).symm
    · rintro ⟨c, rfl⟩
      rw [Submodule.coe_smul, map_smul, uProj_single_zero, smul_zero]
  have hne : (⟨Pi.single 0 1, he⟩ : U) ≠ 0 := fun h =>
    single_zero_ne_zero_UV (congrArg Subtype.val h)
  rw [hker, finrank_span_singleton hne] at h
  exact h

theorem le_of_map_uProj_le {U U' : Submodule K UV} (hU : ∀ v ∈ U, uHerm v v = 0)
    (hU' : ∀ v ∈ U', uHerm v v = 0) (he : (Pi.single 0 1 : UV) ∈ U)
    (he' : (Pi.single 0 1 : UV) ∈ U') (h : U.map uProj ≤ U'.map uProj) : U ≤ U' := by
  intro v hv
  obtain ⟨w, hw, hwv⟩ := h (Submodule.mem_map_of_mem hv)
  have h0 : uProj (v - w) = 0 := by rw [map_sub, hwv, sub_self]
  have h3 : (v - w) 3 = 0 := by
    rw [Pi.sub_apply, v3_eq_zero_of_uIso hU he hv, v3_eq_zero_of_uIso hU' he' hw, sub_zero]
  have hvw : v - w ∈ U' := by
    rw [eq_smul_of_uProj_eq_zero h3 h0]
    exact Submodule.smul_mem _ _ he'
  have : v = (v - w) + w := by abel
  rw [this]
  exact U'.add_mem hvw hw

theorem eq_of_map_uProj_eq {U U' : Submodule K UV} (hU : ∀ v ∈ U, uHerm v v = 0)
    (hU' : ∀ v ∈ U', uHerm v v = 0) (he : (Pi.single 0 1 : UV) ∈ U)
    (he' : (Pi.single 0 1 : UV) ∈ U') (h : U.map uProj = U'.map uProj) : U = U' :=
  le_antisymm (le_of_map_uProj_le hU hU' he he' h.le) (le_of_map_uProj_le hU' hU he' he h.ge)

theorem isTotallyIsotropic_map_uProj {U : Submodule K UV} (hU : ∀ v ∈ U, uHerm v v = 0)
    (he : (Pi.single 0 1 : UV) ∈ U) : C2E6Overlap.IsTotallyIsotropic (U.map uProj) := by
  rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
  rw [herm_uProj (v3_eq_zero_of_uIso hU he hv) (v3_eq_zero_of_uIso hU he hw)]
  exact uHerm_eq_zero_of_isTI hU hv hw

@[expose] def uLift : C2E6Overlap.V →ₗ[K] UV where
  toFun w := ![0, w 0, w 1, 0, w 3, w 2]
  map_add' v w := by funext i; fin_cases i <;> simp
  map_smul' c v := by funext i; fin_cases i <;> simp

theorem uProj_uLift (w : C2E6Overlap.V) : uProj (uLift w) = w := by
  funext i
  fin_cases i <;> rfl

theorem uProj_comp_uLift : uProj ∘ₗ uLift = LinearMap.id :=
  LinearMap.ext uProj_uLift

theorem uHerm_uLift (w w' : C2E6Overlap.V) :
    uHerm (uLift w) (uLift w') = C2E6Overlap.herm w w' := by
  rw [← herm_uProj rfl rfl, uProj_uLift, uProj_uLift]

theorem uIso_sup_map_uLift {U' : Submodule K C2E6Overlap.V}
    (hU' : C2E6Overlap.IsTotallyIsotropic U') :
    ∀ v ∈ cspan K {0} ⊔ U'.map uLift, uHerm v v = 0 := by
  intro v hv
  rw [cspan_singleton] at hv
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hw
  have h1 : uHerm (Pi.single 0 1) (uLift y) = 0 := by
    rw [uHerm_eq_zero_comm, uHerm_single_zero]
    rfl
  have h2 : uHerm (uLift y) (Pi.single 0 1) = 0 := by rw [uHerm_single_zero]; rfl
  simp only [uHerm_add_left, uHerm_add_right, uHerm_smul_left, uHerm_smul_right,
    uHerm_self_single_zero, h1, h2, uHerm_uLift, hU' y hy y hy]
  ring

theorem map_uProj_sup_map_uLift (U' : Submodule K C2E6Overlap.V) :
    (cspan K {0} ⊔ U'.map uLift).map uProj = U' := by
  rw [Submodule.map_sup, map_cspan_singleton, uProj_single_zero,
    Submodule.span_singleton_eq_bot.mpr rfl, bot_sup_eq, ← Submodule.map_comp,
    uProj_comp_uLift, Submodule.map_id]

theorem single_zero_mem_sup_uLift (U' : Submodule K C2E6Overlap.V) :
    (Pi.single 0 1 : UV) ∈ cspan K {0} ⊔ U'.map uLift :=
  Submodule.mem_sup_left (single_mem_cspan (Finset.mem_singleton_self 0))

theorem PFlag.single_zero_mem_V₂_U {x : PFlag UData} (h : x.V₁ = cspan K {0}) :
    (Pi.single 0 1 : UV) ∈ x.V₂ :=
  x.le₁₂ (h ▸ single_mem_cspan (Finset.mem_singleton_self 0))

theorem PFlag.uIso_V₂ (x : PFlag UData) : ∀ v ∈ x.V₂, uHerm v v = 0 :=
  fun v hv => x.isTI v (x.le₂₃ hv)

theorem PFlag.finrank_map_uProj_V₂ {x : PFlag UData} (h : x.V₁ = cspan K {0}) :
    finrank K (x.V₂.map uProj) = 1 := by
  have := finrank_map_uProj_add_one x.uIso_V₂ (PFlag.single_zero_mem_V₂_U h)
  rw [x.finrank₂] at this
  omega

theorem PFlag.finrank_map_uProj_V₃ {x : PFlag UData} (h : x.V₁ = cspan K {0}) :
    finrank K (x.V₃.map uProj) = 2 := by
  have := finrank_map_uProj_add_one x.isTI (x.le₂₃ (PFlag.single_zero_mem_V₂_U h))
  rw [x.finrank₃] at this
  omega

theorem PFlag.isTotallyIsotropic_map_uProj_V₂ {x : PFlag UData} (h : x.V₁ = cspan K {0}) :
    C2E6Overlap.IsTotallyIsotropic (x.V₂.map uProj) :=
  isTotallyIsotropic_map_uProj x.uIso_V₂ (PFlag.single_zero_mem_V₂_U h)

theorem PFlag.isTotallyIsotropic_map_uProj_V₃ {x : PFlag UData} (h : x.V₁ = cspan K {0}) :
    C2E6Overlap.IsTotallyIsotropic (x.V₃.map uProj) :=
  isTotallyIsotropic_map_uProj x.isTI (x.le₂₃ (PFlag.single_zero_mem_V₂_U h))

@[expose] noncomputable def uQFlag (x : PFlag UData) (h : x.V₁ = cspan K {0}) : QFlag where
  pt := ⟨C2E6Overlap.pointMap (x.V₃.map uProj),
    (C2E6Overlap.bijOn_pointMap.mapsTo ⟨PFlag.isTotallyIsotropic_map_uProj_V₃ h,
      PFlag.finrank_map_uProj_V₃ h⟩).1,
    Or.inl (C2E6Overlap.bijOn_pointMap.mapsTo ⟨PFlag.isTotallyIsotropic_map_uProj_V₃ h,
      PFlag.finrank_map_uProj_V₃ h⟩).2⟩
  line := ⟨C2E6Overlap.lineMap (x.V₂.map uProj),
    (C2E6Overlap.bijOn_lineMap.mapsTo ⟨PFlag.isTotallyIsotropic_map_uProj_V₂ h,
      PFlag.finrank_map_uProj_V₂ h⟩).1,
    Or.inr (C2E6Overlap.bijOn_lineMap.mapsTo ⟨PFlag.isTotallyIsotropic_map_uProj_V₂ h,
      PFlag.finrank_map_uProj_V₂ h⟩).2⟩
  finrank_pt := (C2E6Overlap.bijOn_pointMap.mapsTo ⟨PFlag.isTotallyIsotropic_map_uProj_V₃ h,
      PFlag.finrank_map_uProj_V₃ h⟩).2
  finrank_line := (C2E6Overlap.bijOn_lineMap.mapsTo ⟨PFlag.isTotallyIsotropic_map_uProj_V₂ h,
      PFlag.finrank_map_uProj_V₂ h⟩).2
  pt_le_line := (C2E6Overlap.le_iff_pointMap_le_lineMap (PFlag.isTotallyIsotropic_map_uProj_V₂ h)
    (PFlag.finrank_map_uProj_V₂ h) (PFlag.isTotallyIsotropic_map_uProj_V₃ h)
    (PFlag.finrank_map_uProj_V₃ h)).mp (Submodule.map_mono x.le₂₃)

variable {C : Type*}

open _root_.Classical in
@[expose] noncomputable def uQuadModel (f : C → PFlag UData) (y : C) : QFlag :=
  if h : (f y).V₁ = cspan K {0} then uQFlag (f y) h
  else (exists_qflag_pt (v := C2E6Overlap.ptVertex 0) (C2E6Overlap.finrank_ptSub 0)).choose

theorem uQuadModel_pt {f : C → PFlag UData} {y : C} (h : (f y).V₁ = cspan K {0}) :
    (uQuadModel f y).pt.1 = C2E6Overlap.pointMap ((f y).V₃.map uProj) := by
  rw [uQuadModel, dite_eq_left h]
  rfl

theorem uQuadModel_line {f : C → PFlag UData} {y : C} (h : (f y).V₁ = cspan K {0}) :
    (uQuadModel f y).line.1 = C2E6Overlap.lineMap ((f y).V₂.map uProj) := by
  rw [uQuadModel, dite_eq_left h]
  rfl

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {δ : C → C → W} {p l π : ι} (hpl : p ≠ l) (hlπ : l ≠ π) (hpπ : p ≠ π) {f : C → PFlag UData}
  (hf : IsChamberModel cs δ (polarChamber UData p l π) f) {c₀ : C} (hc₀ : f c₀ = uC0)
include hpl hlπ hpπ hf hc₀

theorem mem_residue_lπ_uC0 {y : C} : y ∈ residue cs δ {l, π} c₀ ↔ (f y).V₁ = cspan K {0} := by
  rw [polar_mem_residue_lπ hf hpl hlπ hpπ, hc₀]
  rfl

theorem isModelResidue_uQuadModel :
    IsModelResidue cs δ QFlag.SameLine QFlag.SamePt π l c₀ (uQuadModel f) := by
  have hR : ∀ y, y ∈ residue cs δ {π, l} c₀ ↔ (f y).V₁ = cspan K {0} := fun y => by
    rw [Set.pair_comm]
    exact mem_residue_lπ_uC0 hpl hlπ hpπ hf hc₀
  have hinjP : ∀ {y z : C}, (f y).V₁ = cspan K {0} → (f z).V₁ = cspan K {0} →
      (C2E6Overlap.pointMap ((f y).V₃.map uProj) = C2E6Overlap.pointMap ((f z).V₃.map uProj) ↔
        (f y).V₃ = (f z).V₃) := by
    intro y z hy hz
    refine ⟨fun e => ?_, fun e => by rw [e]⟩
    have e' := C2E6Overlap.bijOn_pointMap.injOn
      ⟨PFlag.isTotallyIsotropic_map_uProj_V₃ hy, PFlag.finrank_map_uProj_V₃ hy⟩
      ⟨PFlag.isTotallyIsotropic_map_uProj_V₃ hz, PFlag.finrank_map_uProj_V₃ hz⟩ e
    exact eq_of_map_uProj_eq (f y).isTI (f z).isTI ((f y).le₂₃ (PFlag.single_zero_mem_V₂_U hy))
      ((f z).le₂₃ (PFlag.single_zero_mem_V₂_U hz)) e'
  have hinjL : ∀ {y z : C}, (f y).V₁ = cspan K {0} → (f z).V₁ = cspan K {0} →
      (C2E6Overlap.lineMap ((f y).V₂.map uProj) = C2E6Overlap.lineMap ((f z).V₂.map uProj) ↔
        (f y).V₂ = (f z).V₂) := by
    intro y z hy hz
    refine ⟨fun e => ?_, fun e => by rw [e]⟩
    have e' := C2E6Overlap.bijOn_lineMap.injOn
      ⟨PFlag.isTotallyIsotropic_map_uProj_V₂ hy, PFlag.finrank_map_uProj_V₂ hy⟩
      ⟨PFlag.isTotallyIsotropic_map_uProj_V₂ hz, PFlag.finrank_map_uProj_V₂ hz⟩ e
    exact eq_of_map_uProj_eq (f y).uIso_V₂ (f z).uIso_V₂ (PFlag.single_zero_mem_V₂_U hy)
      (PFlag.single_zero_mem_V₂_U hz) e'
  refine ⟨⟨fun _ _ => Set.mem_univ _, fun y hy z hz e => ?_, fun F _ => ?_⟩,
    fun y hy z hz => ?_⟩
  · have hy' := (hR y).mp hy
    have hz' := (hR z).mp hz
    have e1 := congrArg (fun F : QFlag => F.pt.1) e
    have e2 := congrArg (fun F : QFlag => F.line.1) e
    simp only [uQuadModel_pt hy', uQuadModel_pt hz'] at e1
    simp only [uQuadModel_line hy', uQuadModel_line hz'] at e2
    exact hf.1.1 (PFlag.ext (hy'.trans hz'.symm) ((hinjL hy' hz').mp e2) ((hinjP hy' hz').mp e1))
  ·
    obtain ⟨P, ⟨hP, hP2⟩, hPF⟩ := C2E6Overlap.bijOn_pointMap.surjOn
      (show F.pt.1 ∈ {U : Submodule (ZMod 2) C2E6Overlap.X |
        C2E6Overlap.IsTotallySingular U ∧ finrank (ZMod 2) U = 1} from ⟨F.pt.2.1, F.finrank_pt⟩)
    obtain ⟨ℓ, ⟨hℓ, hℓ1⟩, hℓF⟩ := C2E6Overlap.bijOn_lineMap.surjOn
      (show F.line.1 ∈ {U : Submodule (ZMod 2) C2E6Overlap.X |
        C2E6Overlap.IsTotallySingular U ∧ finrank (ZMod 2) U = 2} from
          ⟨F.line.2.1, F.finrank_line⟩)
    have hℓP : ℓ ≤ P := (C2E6Overlap.le_iff_pointMap_le_lineMap hℓ hℓ1 hP hP2).mpr
      (by rw [hPF, hℓF]; exact F.pt_le_line)
    have hiso3 := uIso_sup_map_uLift hP
    have hd2 : finrank K ↥(cspan K {0} ⊔ ℓ.map uLift) = 2 := by
      have h := finrank_map_uProj_add_one (uIso_sup_map_uLift hℓ) (single_zero_mem_sup_uLift ℓ)
      rw [map_uProj_sup_map_uLift, hℓ1] at h
      exact h.symm
    have hd3 : finrank K ↥(cspan K {0} ⊔ P.map uLift) = 3 := by
      have h := finrank_map_uProj_add_one hiso3 (single_zero_mem_sup_uLift P)
      rw [map_uProj_sup_map_uLift, hP2] at h
      exact h.symm
    obtain ⟨y, hy⟩ := hf.1.2 ⟨cspan K {0}, cspan K {0} ⊔ ℓ.map uLift, cspan K {0} ⊔ P.map uLift,
      by rw [finrank_cspan]; rfl, hd2, hd3, le_sup_left,
      sup_le_sup_left (Submodule.map_mono hℓP) _, hiso3⟩
    have hy1 : (f y).V₁ = cspan K {0} := by rw [hy]
    refine ⟨y, (hR y).mpr hy1, QFlag.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
    · rw [uQuadModel_pt hy1, hy]
      change C2E6Overlap.pointMap ((cspan K {0} ⊔ P.map uLift).map uProj) = F.pt.1
      rw [map_uProj_sup_map_uLift, hPF]
    · rw [uQuadModel_line hy1, hy]
      change C2E6Overlap.lineMap ((cspan K {0} ⊔ ℓ.map uLift).map uProj) = F.line.1
      rw [map_uProj_sup_map_uLift, hℓF]
  · have hy' := (hR y).mp hy
    have hz' := (hR z).mp hz
    have hsl : QFlag.SameLine (uQuadModel f y) (uQuadModel f z) ↔ (f y).V₂ = (f z).V₂ := by
      rw [QFlag.SameLine, ← hinjL hy' hz', ← uQuadModel_line hy', ← uQuadModel_line hz']
      exact Subtype.ext_iff
    have hsp : QFlag.SamePt (uQuadModel f y) (uQuadModel f z) ↔ (f y).V₃ = (f z).V₃ := by
      rw [QFlag.SamePt, ← hinjP hy' hz', ← uQuadModel_pt hy', ← uQuadModel_pt hz']
      exact Subtype.ext_iff
    rw [hf.2, hf.2, polarChamber_adj_l hpl, polarChamber_adj_π hpπ hlπ, hsl, hsp]
    simp only [hy', hz', true_and]

theorem isQuadrangleFlagResidue_uC0 : IsQuadrangleFlagResidue cs δ π l c₀ :=
  ⟨_, isModelResidue_uQuadModel hpl hlπ hpπ hf hc₀⟩

omit hpl hlπ hpπ hf hc₀ in
@[expose] def uRho : UV →ₗ[K] (Fin 3 → K) where
  toFun v := ![v 0, v 1, v 2]
  map_add' v w := by funext i; fin_cases i <;> rfl
  map_smul' c v := by funext i; fin_cases i <;> rfl

omit [Group W] hpl hlπ hpπ hf in
theorem uRho_injOn : Set.InjOn uRho (f c₀).V₃ := by
  intro v hv w hw h
  rw [hc₀] at hv hw
  change v ∈ cspan K {0, 1, 2} at hv
  change w ∈ cspan K {0, 1, 2} at hw
  rw [mem_cspan] at hv hw
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  all_goals
    simp only [Fin.reduceFinMk, Fin.isValue]
    rw [hv _ (by decide), hw _ (by decide)]

theorem isPlaneFlagResidue_uC0 : IsPlaneFlagResidue cs δ K p l c₀ :=
  isPlaneFlagResidue_polar hf hpl hlπ hpπ uRho (uRho_injOn hc₀)

end CFSG.Monster.B.Geometry

module

public import CFSG.Monster.B.Geometry.OrthBuilding
public import CFSG.Monster.B.Geometry.QuadrangleModel

public section

namespace CFSG.Monster.B.Geometry

open Module CoxeterSystem CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding
open CFSG.LieType.Chevalley.C2E6Overlap (X Q QVertex IsTotallySingular)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem oPolar_single_zero (v : OV) : oPolar v (Pi.single 0 1) = v 3 := by
  simp [oPolar]

theorem oQ_single_zero : oQ (Pi.single 0 1) = 0 := by simp [oQ_apply]

theorem oProj_single_zero : oProj (Pi.single 0 1) = 0 := by
  funext i
  fin_cases i <;> rfl

theorem v3_eq_zero_of_isTSo {U : Submodule (ZMod 2) OV} (hU : IsTSo U)
    (he : (Pi.single 0 1 : OV) ∈ U) {v : OV} (hv : v ∈ U) : v 3 = 0 := by
  rw [← oPolar_single_zero v]
  exact oPolar_eq_zero_of_isTSo hU hv he

theorem finrank_map_oProj_add_one {U : Submodule (ZMod 2) OV} (hU : IsTSo U)
    (he : (Pi.single 0 1 : OV) ∈ U) :
    finrank (ZMod 2) (U.map oProj) + 1 = finrank (ZMod 2) U := by
  have hle := finrank_le_finrank_map_oProj_add_one fun v hv => v3_eq_zero_of_isTSo hU he hv
  have h := LinearMap.finrank_range_add_finrank_ker (oProj.domRestrict U)
  rw [LinearMap.range_domRestrict] at h
  have hmem : (⟨Pi.single 0 1, he⟩ : U) ∈ LinearMap.ker (oProj.domRestrict U) := by
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply]
    exact oProj_single_zero
  have hne : (⟨Pi.single 0 1, he⟩ : U) ≠ 0 := fun h =>
    single_zero_ne_zero (congrArg Subtype.val h)
  have hk := Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem _ _).mpr hmem)
  rw [finrank_span_singleton hne] at hk
  omega

theorem le_of_map_oProj_le {U U' : Submodule (ZMod 2) OV} (hU : IsTSo U) (hU' : IsTSo U')
    (he : (Pi.single 0 1 : OV) ∈ U) (he' : (Pi.single 0 1 : OV) ∈ U')
    (h : U.map oProj ≤ U'.map oProj) : U ≤ U' := by
  intro v hv
  obtain ⟨w, hw, hwv⟩ := h (Submodule.mem_map_of_mem hv)
  have h0 : oProj (v - w) = 0 := by rw [map_sub, hwv, sub_self]
  have h3 : (v - w) 3 = 0 := by
    rw [Pi.sub_apply, v3_eq_zero_of_isTSo hU he hv, v3_eq_zero_of_isTSo hU' he' hw, sub_zero]
  have hvw : v - w ∈ U' := by
    rw [eq_smul_of_oProj_eq_zero h3 h0]
    exact Submodule.smul_mem _ _ he'
  have : v = (v - w) + w := by abel
  rw [this]
  exact U'.add_mem hvw hw

theorem eq_of_map_oProj_eq {U U' : Submodule (ZMod 2) OV} (hU : IsTSo U) (hU' : IsTSo U')
    (he : (Pi.single 0 1 : OV) ∈ U) (he' : (Pi.single 0 1 : OV) ∈ U')
    (h : U.map oProj = U'.map oProj) : U = U' :=
  le_antisymm (le_of_map_oProj_le hU hU' he he' h.le) (le_of_map_oProj_le hU' hU he' he h.ge)

@[expose] def oLift : X →ₗ[ZMod 2] OV where
  toFun x := ![0, x 0, x 1, 0, x 2, x 3, x 4, x 5]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' c x := by funext i; fin_cases i <;> simp

theorem oProj_oLift (x : X) : oProj (oLift x) = x := by
  funext i
  fin_cases i <;> rfl

theorem oQ_oLift (x : X) : oQ (oLift x) = Q x := by
  rw [oQ_apply, C2E6Overlap.Q_apply]
  simp [oLift]

theorem oProj_comp_oLift : oProj ∘ₗ oLift = LinearMap.id :=
  LinearMap.ext oProj_oLift

theorem isTSo_sup_map_oLift {U' : Submodule (ZMod 2) X} (hU' : IsTotallySingular U') :
    IsTSo (cspan (ZMod 2) {0} ⊔ U'.map oLift) := by
  intro v hv
  rw [cspan_singleton] at hv
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hw
  rw [oQ_add, oQ_smul, oQ_single_zero, oQ_oLift, hU' y hy, oPolar_smul_left, oPolar_comm,
    oPolar_single_zero]
  change c * c * 0 + 0 + c * 0 = 0
  ring

theorem map_oProj_sup_map_oLift (U' : Submodule (ZMod 2) X) :
    (cspan (ZMod 2) {0} ⊔ U'.map oLift).map oProj = U' := by
  rw [Submodule.map_sup, map_cspan_singleton, oProj_single_zero,
    Submodule.span_singleton_eq_bot.mpr rfl, bot_sup_eq, ← Submodule.map_comp,
    oProj_comp_oLift, Submodule.map_id]

theorem single_zero_mem_sup (U' : Submodule (ZMod 2) X) :
    (Pi.single 0 1 : OV) ∈ cspan (ZMod 2) {0} ⊔ U'.map oLift :=
  Submodule.mem_sup_left (single_mem_cspan (Finset.mem_singleton_self 0))

@[expose] noncomputable def oQVertex (U : Submodule (ZMod 2) OV) (hU : IsTSo U)
    (he : (Pi.single 0 1 : OV) ∈ U)
    (hd : finrank (ZMod 2) U = 2 ∨ finrank (ZMod 2) U = 3) : QVertex :=
  ⟨U.map oProj, isTotallySingular_map_oProj hU fun _ hv => v3_eq_zero_of_isTSo hU he hv, by
    have := finrank_map_oProj_add_one hU he
    omega⟩

theorem PFlag.single_zero_mem_V₂ {x : PFlag OData} (h : x.V₁ = cspan (ZMod 2) {0}) :
    (Pi.single 0 1 : OV) ∈ x.V₂ :=
  x.le₁₂ (h ▸ single_mem_cspan (Finset.mem_singleton_self 0))

theorem PFlag.isTSo_V₂ (x : PFlag OData) : IsTSo x.V₂ := fun v hv => x.isTI v (x.le₂₃ hv)

@[expose] noncomputable def oQFlag (x : PFlag OData) (h : x.V₁ = cspan (ZMod 2) {0}) : QFlag where
  pt := oQVertex x.V₂ x.isTSo_V₂ (PFlag.single_zero_mem_V₂ h) (Or.inl x.finrank₂)
  line := oQVertex x.V₃ x.isTI (x.le₂₃ (PFlag.single_zero_mem_V₂ h)) (Or.inr x.finrank₃)
  finrank_pt := by
    have := finrank_map_oProj_add_one x.isTSo_V₂ (PFlag.single_zero_mem_V₂ h)
    change finrank (ZMod 2) (x.V₂.map oProj) = 1
    rw [x.finrank₂] at this
    omega
  finrank_line := by
    have := finrank_map_oProj_add_one x.isTI (x.le₂₃ (PFlag.single_zero_mem_V₂ h))
    change finrank (ZMod 2) (x.V₃.map oProj) = 2
    rw [x.finrank₃] at this
    omega
  pt_le_line := Submodule.map_mono x.le₂₃

@[expose] def qBase : QFlag :=
  ⟨C2E6Overlap.ptVertex 0, C2E6Overlap.lnVertex 0, C2E6Overlap.finrank_ptSub 0,
    C2E6Overlap.finrank_lnSub 0, C2E6Overlap.ptSub_le_lnSub_iff.mpr (by decide)⟩

variable {C : Type*}

open _root_.Classical in
@[expose] noncomputable def oQuadModel (f : C → PFlag OData) (y : C) : QFlag :=
  if h : (f y).V₁ = cspan (ZMod 2) {0} then oQFlag (f y) h else qBase

theorem oQuadModel_eq {f : C → PFlag OData} {y : C} (h : (f y).V₁ = cspan (ZMod 2) {0}) :
    oQuadModel f y = oQFlag (f y) h := by
  rw [oQuadModel, dite_eq_left h]

theorem oQuadModel_pt {f : C → PFlag OData} {y : C} (h : (f y).V₁ = cspan (ZMod 2) {0}) :
    (oQuadModel f y).pt.1 = (f y).V₂.map oProj := by
  rw [oQuadModel_eq h]
  rfl

theorem oQuadModel_line {f : C → PFlag OData} {y : C} (h : (f y).V₁ = cspan (ZMod 2) {0}) :
    (oQuadModel f y).line.1 = (f y).V₃.map oProj := by
  rw [oQuadModel_eq h]
  rfl

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {δ : C → C → W} {p l π : ι} (hpl : p ≠ l) (hlπ : l ≠ π) (hpπ : p ≠ π) {f : C → PFlag OData}
  (hf : IsChamberModel cs δ (polarChamber OData p l π) f) {c₀ : C} (hc₀ : f c₀ = oC0)
include hpl hlπ hpπ hf hc₀

theorem mem_residue_lπ_oC0 {y : C} :
    y ∈ residue cs δ {l, π} c₀ ↔ (f y).V₁ = cspan (ZMod 2) {0} := by
  rw [polar_mem_residue_lπ hf hpl hlπ hpπ, hc₀]
  rfl

theorem isModelResidue_oQuadModel :
    IsModelResidue cs δ QFlag.SameLine QFlag.SamePt l π c₀ (oQuadModel f) := by
  have hR := fun y => mem_residue_lπ_oC0 hpl hlπ hpπ hf hc₀ (y := y)
  refine ⟨⟨fun _ _ => Set.mem_univ _, fun y hy z hz e => ?_, fun F _ => ?_⟩,
    fun y hy z hz => ?_⟩
  · have hy' := (hR y).mp hy
    have hz' := (hR z).mp hz
    have e1 := congrArg (fun F : QFlag => F.pt.1) e
    have e2 := congrArg (fun F : QFlag => F.line.1) e
    simp only [oQuadModel_pt hy', oQuadModel_pt hz'] at e1
    simp only [oQuadModel_line hy', oQuadModel_line hz'] at e2
    refine hf.1.1 (PFlag.ext (hy'.trans hz'.symm) ?_ ?_)
    · exact eq_of_map_oProj_eq (f y).isTSo_V₂ (f z).isTSo_V₂ (PFlag.single_zero_mem_V₂ hy')
        (PFlag.single_zero_mem_V₂ hz') e1
    · exact eq_of_map_oProj_eq (f y).isTI (f z).isTI
        ((f y).le₂₃ (PFlag.single_zero_mem_V₂ hy')) ((f z).le₂₃ (PFlag.single_zero_mem_V₂ hz')) e2
  ·
    have hts3 := isTSo_sup_map_oLift F.line.2.1
    have hd2 : finrank (ZMod 2) ↥(cspan (ZMod 2) {0} ⊔ F.pt.1.map oLift) = 2 := by
      have h := finrank_map_oProj_add_one (isTSo_sup_map_oLift F.pt.2.1)
        (single_zero_mem_sup F.pt.1)
      rw [map_oProj_sup_map_oLift] at h
      erw [F.finrank_pt] at h
      exact h.symm
    have hd3 : finrank (ZMod 2) ↥(cspan (ZMod 2) {0} ⊔ F.line.1.map oLift) = 3 := by
      have h := finrank_map_oProj_add_one hts3 (single_zero_mem_sup F.line.1)
      rw [map_oProj_sup_map_oLift] at h
      erw [F.finrank_line] at h
      exact h.symm
    obtain ⟨y, hy⟩ := hf.1.2 ⟨cspan (ZMod 2) {0}, cspan (ZMod 2) {0} ⊔ F.pt.1.map oLift,
      cspan (ZMod 2) {0} ⊔ F.line.1.map oLift, by rw [finrank_cspan]; rfl, hd2, hd3,
      le_sup_left, sup_le_sup_left (Submodule.map_mono F.pt_le_line) _, hts3⟩
    have hy1 : (f y).V₁ = cspan (ZMod 2) {0} := by rw [hy]
    refine ⟨y, (hR y).mpr hy1, QFlag.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
    · rw [oQuadModel_pt hy1, hy]
      exact map_oProj_sup_map_oLift _
    · rw [oQuadModel_line hy1, hy]
      exact map_oProj_sup_map_oLift _
  · have hy' := (hR y).mp hy
    have hz' := (hR z).mp hz
    have hinj2 : (f y).V₂.map oProj = (f z).V₂.map oProj ↔ (f y).V₂ = (f z).V₂ :=
      ⟨eq_of_map_oProj_eq (f y).isTSo_V₂ (f z).isTSo_V₂ (PFlag.single_zero_mem_V₂ hy')
        (PFlag.single_zero_mem_V₂ hz'), fun h => h ▸ rfl⟩
    have hinj3 : (f y).V₃.map oProj = (f z).V₃.map oProj ↔ (f y).V₃ = (f z).V₃ :=
      ⟨eq_of_map_oProj_eq (f y).isTI (f z).isTI ((f y).le₂₃ (PFlag.single_zero_mem_V₂ hy'))
        ((f z).le₂₃ (PFlag.single_zero_mem_V₂ hz')), fun h => h ▸ rfl⟩
    have hsl : QFlag.SameLine (oQuadModel f y) (oQuadModel f z) ↔ (f y).V₃ = (f z).V₃ := by
      rw [QFlag.SameLine, ← hinj3, ← oQuadModel_line hy', ← oQuadModel_line hz']
      exact Subtype.ext_iff
    have hsp : QFlag.SamePt (oQuadModel f y) (oQuadModel f z) ↔ (f y).V₂ = (f z).V₂ := by
      rw [QFlag.SamePt, ← hinj2, ← oQuadModel_pt hy', ← oQuadModel_pt hz']
      exact Subtype.ext_iff
    rw [hf.2, hf.2, polarChamber_adj_l hpl, polarChamber_adj_π hpπ hlπ, hsl, hsp]
    simp only [hy', hz', true_and]

theorem isQuadrangleFlagResidue_oC0 : IsQuadrangleFlagResidue cs δ l π c₀ :=
  ⟨_, isModelResidue_oQuadModel hpl hlπ hpπ hf hc₀⟩

omit [Group W] hpl hlπ hpπ hf in
theorem oQuadModel_c0 : (oQuadModel f c₀).pt.1 = (ZMod 2) ∙ C2E6Overlap.e₁ ∧
    (oQuadModel f c₀).line.1 = Submodule.span (ZMod 2) {C2E6Overlap.e₁, C2E6Overlap.e₂} := by
  have h1 : (f c₀).V₁ = cspan (ZMod 2) {0} := by rw [hc₀]; rfl
  have he1 : oProj (Pi.single 1 1) = C2E6Overlap.e₁ := by funext i; fin_cases i <;> rfl
  have he2 : oProj (Pi.single 2 1) = C2E6Overlap.e₂ := by funext i; fin_cases i <;> rfl
  rw [oQuadModel_pt h1, oQuadModel_line h1, hc₀]
  refine ⟨?_, ?_⟩
  · change (cspan (ZMod 2) {0, 1}).map oProj = _
    rw [map_cspan_insert, map_cspan_singleton, oProj_single_zero, he1,
      Submodule.span_singleton_eq_bot.mpr rfl, bot_sup_eq]
  · change (cspan (ZMod 2) {0, 1, 2}).map oProj = _
    rw [map_cspan_insert, map_cspan_insert, map_cspan_singleton, oProj_single_zero, he1, he2,
      Submodule.span_singleton_eq_bot.mpr rfl, bot_sup_eq, Submodule.span_insert]

omit [Group W] hpl hlπ hpπ hf hc₀ in
theorem oQuadModel_p0 {q : C} (hq : f q = oFlag {0} {0, 4} {0, 4, 5}) :
    (oQuadModel f q).pt.1 = (ZMod 2) ∙ C2E6Overlap.f₁ ∧
    (oQuadModel f q).line.1 = Submodule.span (ZMod 2) {C2E6Overlap.f₁, C2E6Overlap.f₂} := by
  have h1 : (f q).V₁ = cspan (ZMod 2) {0} := by rw [hq]; rfl
  have he4 : oProj (Pi.single 4 1) = C2E6Overlap.f₁ := by funext i; fin_cases i <;> rfl
  have he5 : oProj (Pi.single 5 1) = C2E6Overlap.f₂ := by funext i; fin_cases i <;> rfl
  rw [oQuadModel_pt h1, oQuadModel_line h1, hq]
  refine ⟨?_, ?_⟩
  · change (cspan (ZMod 2) {0, 4}).map oProj = _
    rw [map_cspan_insert, map_cspan_singleton, oProj_single_zero, he4,
      Submodule.span_singleton_eq_bot.mpr rfl, bot_sup_eq]
  · change (cspan (ZMod 2) {0, 4, 5}).map oProj = _
    rw [map_cspan_insert, map_cspan_insert, map_cspan_singleton, oProj_single_zero, he4, he5,
      Submodule.span_singleton_eq_bot.mpr rfl, bot_sup_eq, Submodule.span_insert]

@[expose] def oRho : OV →ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun v := ![v 0, v 1, v 2]
  map_add' v w := by funext i; fin_cases i <;> rfl
  map_smul' c v := by funext i; fin_cases i <;> rfl

omit [Group W] hpl hlπ hpπ hf in
theorem oRho_injOn : Set.InjOn oRho (f c₀).V₃ := by
  intro v hv w hw h
  rw [hc₀] at hv hw
  change v ∈ cspan (ZMod 2) {0, 1, 2} at hv
  change w ∈ cspan (ZMod 2) {0, 1, 2} at hw
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

theorem isPlaneFlagResidue_oC0 : IsPlaneFlagResidue cs δ (ZMod 2) p l c₀ :=
  isPlaneFlagResidue_polar hf hpl hlπ hpπ oRho (oRho_injOn hc₀)

omit [Group W] hpl hlπ hpπ hf hc₀ in
@[expose] def oTailLin (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) : OV →ₗ[ZMod 2] OV where
  toFun v := ![v 0, v 1, v 2, v 3, v 4, v 5, A 0 0 * v 6 + A 0 1 * v 7,
    A 1 0 * v 6 + A 1 1 * v 7]
  map_add' v w := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by funext i; fin_cases i <;> simp <;> ring

omit [Group W] hpl hlπ hpπ hf hc₀ in
theorem oTailLin_apply (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) (v : OV) :
    oTailLin A v = ![v 0, v 1, v 2, v 3, v 4, v 5, A 0 0 * v 6 + A 0 1 * v 7,
      A 1 0 * v 6 + A 1 1 * v 7] := rfl

omit [Group W] hpl hlπ hpπ hf hc₀ in
theorem oQ_oTailLin {A : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hA : A.det ≠ 0) (v : OV) :
    oQ (oTailLin A v) = oQ v := by
  rw [Matrix.det_fin_two] at hA
  have h := C2E6Overlap.tail_norm_invariant (A 0 0) (A 0 1) (A 1 0) (A 1 1) (v 6) (v 7) hA
  rw [oQ_apply, oQ_apply, oTailLin_apply]
  simp only [Matrix.cons_val]
  linear_combination h

omit [Group W] hpl hlπ hpπ hf hc₀ in
theorem oTailLin_mul (A B : Matrix (Fin 2) (Fin 2) (ZMod 2)) (v : OV) :
    oTailLin A (oTailLin B v) = oTailLin (A * B) v := by
  funext i
  fin_cases i <;> simp [oTailLin_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

omit [Group W] hpl hlπ hpπ hf hc₀ in
theorem oTailLin_one (v : OV) : oTailLin 1 v = v := by
  funext i
  fin_cases i <;> simp [oTailLin_apply]

omit [Group W] hpl hlπ hpπ hf hc₀ in
theorem oTailLin_bijective (A : GL (Fin 2) (ZMod 2)) : Function.Bijective (oTailLin A) := by
  refine ⟨fun v w h => ?_, fun w => ⟨oTailLin ↑A⁻¹ w, ?_⟩⟩
  · have := congrArg (oTailLin ↑A⁻¹) h
    rwa [oTailLin_mul, oTailLin_mul, Units.inv_mul, oTailLin_one, oTailLin_one] at this
  · rw [oTailLin_mul, Units.mul_inv, oTailLin_one]

omit [Group W] hpl hlπ hpπ hf hc₀ in
theorem oProj_oTailLin (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) (v : OV) :
    oProj (oTailLin A v) = C2E6Overlap.tailLin A (oProj v) := by
  funext i
  fin_cases i <;> rfl

omit [Group W] hpl hlπ hpπ hf hc₀ in
theorem map_oTailLin_cspan (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) {s : Finset (Fin 8)}
    (h6 : 6 ∉ s) (h7 : 7 ∉ s) : (cspan (ZMod 2) s).map (oTailLin A) = cspan (ZMod 2) s := by
  rw [cspan, Submodule.map_span, Set.image_image]
  congr 1
  refine Set.image_congr fun k hk => ?_
  have hk6 : (6 : Fin 8) ≠ k := fun h => h6 (h ▸ hk)
  have hk7 : (7 : Fin 8) ≠ k := fun h => h7 (h ▸ hk)
  funext i
  rw [oTailLin_apply]
  fin_cases i <;> simp [Pi.single_apply, hk6, hk7]

omit [Group W] hpl hlπ hpπ hf hc₀ in
@[expose] noncomputable def oTailPerm (A : GL (Fin 2) (ZMod 2)) : Equiv.Perm (PFlag OData) :=
  polarFlagPerm (oTailLin A) (oTailLin_bijective A) fun v => by
    rw [oData_iso, oData_iso, oQ_oTailLin (C2E6Overlap.det_ne_zero_of_GL A)]

omit [Group W] hpl hlπ hpπ hf hc₀ in
theorem oTailPerm_oC0 (A : GL (Fin 2) (ZMod 2)) : oTailPerm A oC0 = oC0 :=
  PFlag.ext (map_oTailLin_cspan _ (by decide) (by decide))
    (map_oTailLin_cspan _ (by decide) (by decide)) (map_oTailLin_cspan _ (by decide) (by decide))

omit [Group W] hpl hlπ hpπ hf hc₀ in
theorem oTailPerm_oD0 (A : GL (Fin 2) (ZMod 2)) : oTailPerm A oD0 = oD0 :=
  PFlag.ext (map_oTailLin_cspan _ (by decide) (by decide))
    (map_oTailLin_cspan _ (by decide) (by decide)) (map_oTailLin_cspan _ (by decide) (by decide))

omit [Group W] hpl hlπ hpπ hf hc₀ in
theorem map_oProj_map_oTailLin (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) (U : Submodule (ZMod 2) OV) :
    (U.map (oTailLin A)).map oProj = (U.map oProj).map (C2E6Overlap.tailLin A) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1

omit hpl hlπ hpπ hc₀ in
theorem oQuadModel_oTailPerm (A : GL (Fin 2) (ZMod 2)) {y : C}
    (hy : (f y).V₁ = cspan (ZMod 2) {0}) :
    (f (hf.perm (oTailPerm A) y)).V₁ = cspan (ZMod 2) {0} ∧
    (oQuadModel f (hf.perm (oTailPerm A) y)).pt =
      C2E6Overlap.inducedPerm (C2E6Overlap.tailIso A) (oQuadModel f y).pt ∧
    (oQuadModel f (hf.perm (oTailPerm A) y)).line =
      C2E6Overlap.inducedPerm (C2E6Overlap.tailIso A) (oQuadModel f y).line := by
  have hgy : f (hf.perm (oTailPerm A) y) = oTailPerm A (f y) := hf.apply_perm _ y
  have h1 : (f (hf.perm (oTailPerm A) y)).V₁ = cspan (ZMod 2) {0} := by
    rw [hgy]
    change (f y).V₁.map (oTailLin A) = _
    rw [hy, map_oTailLin_cspan _ (by decide) (by decide)]
  have htail : ((C2E6Overlap.tailIso A).toLinearEquiv : X →ₗ[ZMod 2] X) =
      C2E6Overlap.tailLin A := LinearMap.ext fun _ => rfl
  refine ⟨h1, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [oQuadModel_pt h1, C2E6Overlap.coe_inducedPerm, oQuadModel_pt hy, htail, hgy]
    exact map_oProj_map_oTailLin _ _
  · rw [oQuadModel_line h1, C2E6Overlap.coe_inducedPerm, oQuadModel_line hy, htail, hgy]
    exact map_oProj_map_oTailLin _ _

end CFSG.Monster.B.Geometry

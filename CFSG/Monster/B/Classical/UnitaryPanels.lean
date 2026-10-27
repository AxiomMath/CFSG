module

public import CFSG.Monster.B.Classical.UnitaryPanelsFrame
public import CFSG.LinearAlgebra.LinearGroups.UnitaryTransitivity

public section

namespace CFSG.Monster.B.Classical.UnitaryPanels

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Action

variable {p f : ℕ} (h : UnitaryFieldData p f K) [FiniteDimensional K V]
  {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft) (hV : finrank K V = 6)

@[expose] noncomputable def psuSubspaceAction :
    sesqSpecialUnitaryGroup B ⧸ Subgroup.center (sesqSpecialUnitaryGroup B) →*
      Equiv.Perm (Submodule K V) :=
  QuotientGroup.lift _ (MulAction.toPermHom _ _) (center_le_ker_toPermHom h hB hBl hV)

theorem psuSubspaceAction_mk (g : sesqSpecialUnitaryGroup B) (W : Submodule K V) :
    psuSubspaceAction h hB hBl hV (g : sesqSpecialUnitaryGroup B ⧸
        Subgroup.center (sesqSpecialUnitaryGroup B)) W =
      W.map ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) :=
  rfl

@[expose] noncomputable def psuFlagStabilizer (R H T : Submodule K V) :
    Subgroup (sesqSpecialUnitaryGroup B ⧸ Subgroup.center (sesqSpecialUnitaryGroup B)) :=
  (MulAction.stabilizer (Equiv.Perm (Submodule K V)) R).comap (psuSubspaceAction h hB hBl hV) ⊓
    (MulAction.stabilizer (Equiv.Perm (Submodule K V)) H).comap (psuSubspaceAction h hB hBl hV) ⊓
    (MulAction.stabilizer (Equiv.Perm (Submodule K V)) T).comap (psuSubspaceAction h hB hBl hV)

theorem mem_psuFlagStabilizer {R H T : Submodule K V}
    {u : sesqSpecialUnitaryGroup B ⧸ Subgroup.center (sesqSpecialUnitaryGroup B)} :
    u ∈ psuFlagStabilizer h hB hBl hV R H T ↔
      psuSubspaceAction h hB hBl hV u R = R ∧ psuSubspaceAction h hB hBl hV u H = H ∧
        psuSubspaceAction h hB hBl hV u T = T := by
  simp only [psuFlagStabilizer, Subgroup.mem_inf, Subgroup.mem_comap,
    MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, and_assoc]

theorem exists_mem_psuFlagStabilizer {R H T X Y : Submodule K V}
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ sesqSpecialUnitaryGroup B)
    (hR : R.map (g : V →ₗ[K] V) = R) (hH : H.map (g : V →ₗ[K] V) = H)
    (hT : T.map (g : V →ₗ[K] V) = T) (hXY : X.map (g : V →ₗ[K] V) = Y) :
    ∃ u ∈ psuFlagStabilizer h hB hBl hV R H T, psuSubspaceAction h hB hBl hV u X = Y :=
  ⟨((⟨g, hg⟩ : sesqSpecialUnitaryGroup B) :
      sesqSpecialUnitaryGroup B ⧸ Subgroup.center (sesqSpecialUnitaryGroup B)),
    (mem_psuFlagStabilizer h hB hBl hV).2 ⟨hR, hH, hT⟩, hXY⟩

theorem exists_rep_of_mem_psuFlagStabilizer {R H T : Submodule K V}
    {u : sesqSpecialUnitaryGroup B ⧸ Subgroup.center (sesqSpecialUnitaryGroup B)}
    (hu : u ∈ psuFlagStabilizer h hB hBl hV R H T) :
    ∃ g ∈ sesqSpecialUnitaryGroup B, (∀ W : Submodule K V,
      psuSubspaceAction h hB hBl hV u W = W.map (g : V →ₗ[K] V)) ∧
      R.map (g : V →ₗ[K] V) = R ∧ H.map (g : V →ₗ[K] V) = H ∧ T.map (g : V →ₗ[K] V) = T := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨hR, hH, hT⟩ := (mem_psuFlagStabilizer h hB hBl hV).1 hu
  exact ⟨g, g.2, fun W => rfl, hR, hH, hT⟩

omit [FiniteDimensional K V] in
theorem injective_coe_generalLinearGroup (g : LinearMap.GeneralLinearGroup K V) :
    Function.Injective (g : V →ₗ[K] V) := by
  have := (LinearMap.GeneralLinearGroup.generalLinearEquiv K V g).injective
  rwa [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv] at this

theorem mapsTo_panelR {R H T : Submodule K V}
    {u : sesqSpecialUnitaryGroup B ⧸ Subgroup.center (sesqSpecialUnitaryGroup B)}
    (hu : u ∈ psuFlagStabilizer h hB hBl hV R H T) {X : Submodule K V}
    (hX : X ∈ {R' : Submodule K V | finrank K R' = 1 ∧ R' < H ∧ R' ≠ R}) :
    psuSubspaceAction h hB hBl hV u X ∈
      {R' : Submodule K V | finrank K R' = 1 ∧ R' < H ∧ R' ≠ R} := by
  obtain ⟨g, -, hgW, hR, hH, -⟩ := exists_rep_of_mem_psuFlagStabilizer h hB hBl hV hu
  have hinj := injective_coe_generalLinearGroup g
  obtain ⟨hX1, hXH, hXR⟩ := hX
  rw [hgW]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hX1]
    exact LinearEquiv.finrank_map_eq (LinearMap.GeneralLinearGroup.generalLinearEquiv K V g) X
  · rw [← hH]
    exact Submodule.map_strictMono_of_injective hinj hXH
  · intro hEq
    exact hXR (Submodule.map_injective_of_injective hinj (hEq.trans hR.symm))

theorem mapsTo_panelH {R H T : Submodule K V}
    {u : sesqSpecialUnitaryGroup B ⧸ Subgroup.center (sesqSpecialUnitaryGroup B)}
    (hu : u ∈ psuFlagStabilizer h hB hBl hV R H T) {X : Submodule K V}
    (hX : X ∈ {H' : Submodule K V | R < H' ∧ H' < T ∧ finrank K H' = 2 ∧ H' ≠ H}) :
    psuSubspaceAction h hB hBl hV u X ∈
      {H' : Submodule K V | R < H' ∧ H' < T ∧ finrank K H' = 2 ∧ H' ≠ H} := by
  obtain ⟨g, -, hgW, hR, hH, hT⟩ := exists_rep_of_mem_psuFlagStabilizer h hB hBl hV hu
  have hinj := injective_coe_generalLinearGroup g
  obtain ⟨hRX, hXT, hX2, hXH⟩ := hX
  rw [hgW]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hR]
    exact Submodule.map_strictMono_of_injective hinj hRX
  · rw [← hT]
    exact Submodule.map_strictMono_of_injective hinj hXT
  · rw [← hX2]
    exact LinearEquiv.finrank_map_eq (LinearMap.GeneralLinearGroup.generalLinearEquiv K V g) X
  · intro hEq
    exact hXH (Submodule.map_injective_of_injective hinj (hEq.trans hH.symm))

theorem mapsTo_panelT {R H T : Submodule K V}
    {u : sesqSpecialUnitaryGroup B ⧸ Subgroup.center (sesqSpecialUnitaryGroup B)}
    (hu : u ∈ psuFlagStabilizer h hB hBl hV R H T) {X : Submodule K V}
    (hX : X ∈ {T' : Submodule K V | H < T' ∧ finrank K T' = 3 ∧
      (∀ x ∈ T', ∀ y ∈ T', B x y = 0) ∧ T' ≠ T}) :
    psuSubspaceAction h hB hBl hV u X ∈ {T' : Submodule K V | H < T' ∧ finrank K T' = 3 ∧
      (∀ x ∈ T', ∀ y ∈ T', B x y = 0) ∧ T' ≠ T} := by
  obtain ⟨g, hg, hgW, -, hH, hT⟩ := exists_rep_of_mem_psuFlagStabilizer h hB hBl hV hu
  have hinj := injective_coe_generalLinearGroup g
  have hiso := (mem_sesqUnitaryGroup.1 (sesqSpecialUnitaryGroup_le B hg))
  obtain ⟨hHX, hX3, hXi, hXT⟩ := hX
  rw [hgW]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hH]
    exact Submodule.map_strictMono_of_injective hinj hHX
  · rw [← hX3]
    exact LinearEquiv.finrank_map_eq (LinearMap.GeneralLinearGroup.generalLinearEquiv K V g) X
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hiso]
    exact hXi x hx y hy
  · intro hEq
    exact hXT (Submodule.map_injective_of_injective hinj (hEq.trans hT.symm))

end Action

section Dual

variable {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K}

theorem finrank_span_pair_of_dual {u₁ u₂ w₁ w₂ : V} (h11 : B w₁ u₁ = 1) (h12 : B w₁ u₂ = 0)
    (h21 : B w₂ u₁ = 0) (h22 : B w₂ u₂ = 1) : finrank K (Submodule.span K {u₁, u₂}) = 2 := by
  have hli : LinearIndependent K ![u₁, u₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 := congrArg (B w₁) hst
    have e2 := congrArg (B w₂) hst
    simp only [map_add, map_smul, smul_eq_mul, h11, h12, h21, h22, map_zero] at e1 e2
    exact ⟨by simpa using e1, by simpa using e2⟩
  have hrange : Set.range ![u₁, u₂] = {u₁, u₂} := by
    rw [Matrix.range_cons, Matrix.range_cons_empty, Set.singleton_union]
  rw [← hrange, finrank_span_eq_card hli, Fintype.card_fin]

theorem finrank_span_triple_of_dual {u₁ u₂ u₃ w₁ w₂ w₃ : V} (h11 : B w₁ u₁ = 1)
    (h12 : B w₁ u₂ = 0) (h13 : B w₁ u₃ = 0) (h21 : B w₂ u₁ = 0) (h22 : B w₂ u₂ = 1)
    (h23 : B w₂ u₃ = 0) (h31 : B w₃ u₁ = 0) (h32 : B w₃ u₂ = 0) (h33 : B w₃ u₃ = 1) :
    finrank K (Submodule.span K {u₁, u₂, u₃}) = 3 := by
  have hli : LinearIndependent K ![u₁, u₂, u₃] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    have e1 := congrArg (B w₁) hg
    have e2 := congrArg (B w₂) hg
    have e3 := congrArg (B w₃) hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, map_add, map_smul, smul_eq_mul, h11, h12, h13, h21,
      h22, h23, h31, h32, h33, map_zero, mul_zero, mul_one, add_zero, zero_add] at e1 e2 e3
    intro i
    fin_cases i
    exacts [e1, e2, e3]
  have hrange : Set.range ![u₁, u₂, u₃] = {u₁, u₂, u₃} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons_empty, Set.singleton_union,
      Set.singleton_union]
  rw [← hrange, finrank_span_eq_card hli, Fintype.card_fin]

variable [FiniteDimensional K V]

theorem exists_mem_sesqSpecialUnitaryGroup {φ : V →ₗ[K] V}
    (hiso : ∀ x y, B (φ x) (φ y) = B x y) (hdet : LinearMap.det φ = 1) :
    ∃ g ∈ sesqSpecialUnitaryGroup B, (g : V →ₗ[K] V) = φ := by
  have hu : IsUnit φ := (LinearMap.isUnit_iff_isUnit_det φ).2 (by rw [hdet]; exact isUnit_one)
  refine ⟨hu.unit, ?_, hu.unit_spec⟩
  rw [mem_sesqSpecialUnitaryGroup, mem_sesqUnitaryGroup, hu.unit_spec]
  exact ⟨hiso, hdet⟩

theorem map_flag_eq (g : LinearMap.GeneralLinearGroup K V) {e₀ e₁ e₂ : V}
    (h0 : (g : V →ₗ[K] V) e₀ ∈ Submodule.span K {e₀})
    (h1 : (g : V →ₗ[K] V) e₁ ∈ Submodule.span K {e₀, e₁})
    (h2 : (g : V →ₗ[K] V) e₂ ∈ Submodule.span K {e₀, e₁, e₂}) :
    (Submodule.span K {e₀}).map (g : V →ₗ[K] V) = Submodule.span K {e₀} ∧
      (Submodule.span K {e₀, e₁}).map (g : V →ₗ[K] V) = Submodule.span K {e₀, e₁} ∧
      (Submodule.span K {e₀, e₁, e₂}).map (g : V →ₗ[K] V) = Submodule.span K {e₀, e₁, e₂} := by
  have h01 : Submodule.span K {e₀} ≤ Submodule.span K {e₀, e₁} :=
    Submodule.span_mono (by simp)
  have h12 : Submodule.span K {e₀, e₁} ≤ Submodule.span K {e₀, e₁, e₂} :=
    Submodule.span_mono (Set.insert_subset_insert (by simp))
  refine ⟨map_span_eq_of_forall_mem g fun s hs => ?_, map_span_eq_of_forall_mem g fun s hs => ?_,
    map_span_eq_of_forall_mem g fun s hs => ?_⟩
  · rw [Set.mem_singleton_iff.1 hs]
    exact h0
  · rcases hs with rfl | rfl
    · exact h01 h0
    · exact h1
  · rcases hs with rfl | rfl | rfl
    · exact h12 (h01 h0)
    · exact h12 h1
    · exact h2

end Dual

section Field

variable (h : UnitaryFieldData 2 1 K)
include h

private theorem two_eq_zero_K : (2 : K) = 0 := by
  have := h.charP
  exact CharTwo.two_eq_zero

private theorem bar_eq_sq (c : K) : h.bar c = c ^ 2 := by
  rw [h.bar_apply]
  norm_num

private theorem card_eq_four : Nat.card K = 4 := by
  rw [h.card]
  norm_num

private theorem one_mem_traceZero : (1 : K) ∈ h.traceZero := by
  rw [h.mem_traceZero, UnitaryFieldData.trace, map_one, one_add_one_eq_two, two_eq_zero_K h]

private theorem eq_zero_or_eq_one_of_trace (μ : K) (hμ : μ + h.bar μ = 0) : μ = 0 ∨ μ = 1 := by
  rw [bar_eq_sq h] at hμ
  have h2 := two_eq_zero_K h
  rcases mul_eq_zero.1 (show μ * (μ + 1) = 0 by linear_combination hμ) with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination h1 - h2)

private theorem add_self_eq_zero_V (x : V) : x + x = 0 := by
  rw [← two_smul K x, two_eq_zero_K h, zero_smul]

end Field

section Panels

variable (h : UnitaryFieldData 2 1 K) [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K}
  (hB : B.IsSymm) {e f : Fin 3 → V} (he : ∀ i j, B (e i) (e j) = 0)
  (hf : ∀ i j, B (f i) (f j) = 0) (hef : ∀ i j, B (e i) (f j) = if i = j then 1 else 0)

include hB hef

omit [FiniteDimensional K V] in
theorem panelR_eq :
    {R' : Submodule K V | finrank K R' = 1 ∧ R' < Submodule.span K {e 0, e 1} ∧
      R' ≠ Submodule.span K {e 0}} = Set.range fun a : K => Submodule.span K {e 1 + a • e 0} := by
  have hfe := frame_fe h hB hef
  ext R'
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨hR1, hRH, hRne⟩
    obtain ⟨m, hm0, rfl⟩ := exists_eq_span_singleton_of_finrank_eq_one hR1
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 (hRH.le (Submodule.mem_span_singleton_self _))
    by_cases hb : b = 0
    · subst hb
      have ha : a ≠ 0 := by
        rintro rfl
        simp at hm0
      exact absurd (by rw [zero_smul, add_zero, Submodule.span_singleton_smul_eq (IsUnit.mk0 a ha)])
        hRne
    · refine ⟨b⁻¹ * a, ?_⟩
      have : e 1 + (b⁻¹ * a) • e 0 = b⁻¹ • (a • e 0 + b • e 1) := by
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hb, one_smul, add_comm]
      rw [this, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero hb))]
  · rintro ⟨a, rfl⟩
    have hv0 : e 1 + a • e 0 ≠ 0 := by
      intro h0
      have := congrArg (B (f 1)) h0
      simp [hfe] at this
    refine ⟨finrank_span_singleton hv0, lt_of_le_of_ne ?_ ?_, ?_⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.add_mem _ (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · intro hEq
      have hmem : e 0 ∈ Submodule.span K {e 1 + a • e 0} := by
        rw [hEq]
        exact Submodule.subset_span (by simp)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
      have h1 := congrArg (B (f 1)) hc
      have h0 := congrArg (B (f 0)) hc
      simp [hfe] at h1 h0
      simp [h1] at h0
    · intro hEq
      have hmem : e 1 + a • e 0 ∈ Submodule.span K {e 0} := by
        rw [← hEq]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
      have := congrArg (B (f 1)) hc
      simp [hfe] at this

omit [FiniteDimensional K V] in
theorem panelR_injective : Function.Injective fun a : K => Submodule.span K {e 1 + a • e 0} := by
  have hfe := frame_fe h hB hef
  intro a b hab
  simp only at hab
  have hmem : e 1 + a • e 0 ∈ Submodule.span K {e 1 + b • e 0} := by
    rw [← hab]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  have h1 := congrArg (B (f 1)) hc
  have h0 := congrArg (B (f 0)) hc
  simp [hfe] at h1 h0
  rw [← h0, h1, one_mul]

theorem panelH_eq :
    {H' : Submodule K V | Submodule.span K {e 0} < H' ∧ H' < Submodule.span K {e 0, e 1, e 2} ∧
      finrank K H' = 2 ∧ H' ≠ Submodule.span K {e 0, e 1}} =
      Set.range fun a : K => Submodule.span K {e 0, e 2 + a • e 1} := by
  have hfe := frame_fe h hB hef
  have he0 : e 0 ≠ 0 := fun h0 => by
    have := hfe 0 0
    rw [h0, map_zero] at this
    simp at this
  have hR1 : finrank K (Submodule.span K {e 0}) = 1 := finrank_span_singleton he0
  have hH2 : finrank K (Submodule.span K {e 0, e 1}) = 2 :=
    finrank_span_pair_of_dual (B := B) (w₁ := f 0) (w₂ := f 1) (by simp [hfe]) (by simp [hfe])
      (by simp [hfe]) (by simp [hfe])
  have hP2 : ∀ a : K, finrank K (Submodule.span K {e 0, e 2 + a • e 1}) = 2 := fun a =>
    finrank_span_pair_of_dual (B := B) (w₁ := f 0) (w₂ := f 2) (by simp [hfe]) (by simp [hfe])
      (by simp [hfe]) (by simp [hfe])
  have hT3 : finrank K (Submodule.span K {e 0, e 1, e 2}) = 3 :=
    finrank_span_triple_of_dual (B := B) (w₁ := f 0) (w₂ := f 1) (w₃ := f 2) (by simp [hfe])
      (by simp [hfe]) (by simp [hfe]) (by simp [hfe]) (by simp [hfe]) (by simp [hfe])
      (by simp [hfe]) (by simp [hfe]) (by simp [hfe])
  ext H'
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨hRH, hHT, hH'2, hHne⟩
    obtain ⟨m, hmH, hmR⟩ := IsConcreteLE.exists_of_lt hRH
    obtain ⟨a, z, hz, rfl⟩ := Submodule.mem_span_insert.1 (hHT.le hmH)
    obtain ⟨b, c, rfl⟩ := Submodule.mem_span_pair.1 hz
    have he0H : e 0 ∈ H' := hRH.le (Submodule.mem_span_singleton_self _)
    by_cases hc : c = 0
    · exfalso
      subst hc
      apply hHne
      have hsup := sup_span_singleton_eq hRH.le (by rw [hH'2, hR1]) hmH hmR
      refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hH'2, hH2])
      rw [← hsup]
      refine sup_le (Submodule.span_mono (by simp)) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
      rw [zero_smul, add_zero]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · refine ⟨c⁻¹ * b, ?_⟩
      have hx : e 2 + (c⁻¹ * b) • e 1 ∈ H' := by
        have : e 2 + (c⁻¹ * b) • e 1 = c⁻¹ • ((a • e 0 + (b • e 1 + c • e 2)) - a • e 0) := by
          rw [add_sub_cancel_left, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul,
            add_comm]
        rw [this]
        exact H'.smul_mem _ (H'.sub_mem hmH (H'.smul_mem _ he0H))
      refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hP2, hH'2])
      rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact he0H
      · exact hx
  · rintro ⟨a, rfl⟩
    refine ⟨lt_of_le_of_ne (Submodule.span_mono (by simp)) ?_, lt_of_le_of_ne ?_ ?_, hP2 a, ?_⟩
    · intro hEq
      have hmem : e 2 + a • e 1 ∈ Submodule.span K {e 0} := by
        rw [hEq]
        exact Submodule.subset_span (by simp)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
      have := congrArg (B (f 2)) hc
      simp [hfe] at this
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact Submodule.subset_span (by simp)
      · exact Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · intro hEq
      have := hP2 a
      rw [hEq, hT3] at this
      omega
    · intro hEq
      have hmem : e 2 + a • e 1 ∈ Submodule.span K {e 0, e 1} := by
        rw [← hEq]
        exact Submodule.subset_span (by simp)
      obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.1 hmem
      have := congrArg (B (f 2)) hcd
      simp [hfe] at this

omit [FiniteDimensional K V] in
theorem panelH_injective :
    Function.Injective fun a : K => Submodule.span K {e 0, e 2 + a • e 1} := by
  have hfe := frame_fe h hB hef
  intro a b hab
  simp only at hab
  have hmem : e 2 + a • e 1 ∈ Submodule.span K {e 0, e 2 + b • e 1} := by
    rw [← hab]
    exact Submodule.subset_span (by simp)
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.1 hmem
  have h2 := congrArg (B (f 2)) hcd
  have h1 := congrArg (B (f 1)) hcd
  simp [hfe] at h2 h1
  rw [← h1, h2, one_mul]

omit [FiniteDimensional K V] in
include he hf in
theorem isotropic_panelT :
    (∀ x ∈ Submodule.span K {e 0, e 1, f 2}, ∀ y ∈ Submodule.span K {e 0, e 1, f 2},
      B x y = 0) ∧
    ∀ x ∈ Submodule.span K {e 0, e 1, e 2 + f 2}, ∀ y ∈ Submodule.span K {e 0, e 1, e 2 + f 2},
      B x y = 0 := by
  have hfe := frame_fe h hB hef
  have h2 := two_eq_zero_K h
  refine ⟨fun x hx y hy => sesq_eq_zero_of_mem_span_of_forall ?_ hx hy,
    fun x hx y hy => sesq_eq_zero_of_mem_span_of_forall ?_ hx hy⟩
  · rintro s (rfl | rfl | rfl) t (rfl | rfl | rfl) <;> simp [he, hf, hef, hfe]
  · rintro s (rfl | rfl | rfl) t (rfl | rfl | rfl) <;>
      simp [he, hf, hef, hfe, one_add_one_eq_two, h2]

omit [FiniteDimensional K V] in
include he hf in
theorem panelT_ne :
    Submodule.span K {e 0, e 1, f 2} ≠ Submodule.span K {e 0, e 1, e 2 + f 2} := by
  have hfe := frame_fe h hB hef
  intro hEq
  have hmem : e 2 + f 2 ∈ Submodule.span K {e 0, e 1, f 2} := by
    rw [hEq]
    exact Submodule.subset_span (by simp)
  have := (isotropic_panelT h hB he hf hef).1 _ (Submodule.subset_span (by simp) : f 2 ∈ _) _ hmem
  simp [hf, hfe] at this

include he hf in
theorem panelT_eq (hBl : B.SeparatingLeft) (hV : finrank K V = 6) :
    {T' : Submodule K V | Submodule.span K {e 0, e 1} < T' ∧ finrank K T' = 3 ∧
      (∀ x ∈ T', ∀ y ∈ T', B x y = 0) ∧ T' ≠ Submodule.span K {e 0, e 1, e 2}} =
      {Submodule.span K {e 0, e 1, f 2}, Submodule.span K {e 0, e 1, e 2 + f 2}} := by
  have hfe := frame_fe h hB hef
  have hH2 : finrank K (Submodule.span K {e 0, e 1}) = 2 :=
    finrank_span_pair_of_dual (B := B) (w₁ := f 0) (w₂ := f 1) (by simp [hfe]) (by simp [hfe])
      (by simp [hfe]) (by simp [hfe])
  have hT3 : finrank K (Submodule.span K {e 0, e 1, e 2}) = 3 :=
    finrank_span_triple_of_dual (B := B) (w₁ := f 0) (w₂ := f 1) (w₃ := f 2) (by simp [hfe])
      (by simp [hfe]) (by simp [hfe]) (by simp [hfe]) (by simp [hfe]) (by simp [hfe])
      (by simp [hfe]) (by simp [hfe]) (by simp [hfe])
  have hT₁3 : finrank K (Submodule.span K {e 0, e 1, f 2}) = 3 :=
    finrank_span_triple_of_dual (B := B) (w₁ := f 0) (w₂ := f 1) (w₃ := e 2) (by simp [hfe])
      (by simp [hfe]) (by simp [hf]) (by simp [hfe]) (by simp [hfe]) (by simp [hf])
      (by simp [he]) (by simp [he]) (by simp [hef])
  have hT₂3 : finrank K (Submodule.span K {e 0, e 1, e 2 + f 2}) = 3 :=
    finrank_span_triple_of_dual (B := B) (w₁ := f 0) (w₂ := f 1) (w₃ := e 2) (by simp [hfe])
      (by simp [hfe]) (by simp [hfe, hf]) (by simp [hfe]) (by simp [hfe]) (by simp [hfe, hf])
      (by simp [he]) (by simp [he]) (by simp [he, hef])
  have hiso₀ : ∀ x ∈ Submodule.span K {e 0, e 1, e 2}, ∀ y ∈ Submodule.span K {e 0, e 1, e 2},
      B x y = 0 := fun x hx y hy => sesq_eq_zero_of_mem_span_of_forall
    (by rintro s (rfl | rfl | rfl) t (rfl | rfl | rfl) <;> exact he _ _) hx hy
  have hHT₀ : Submodule.span K {e 0, e 1} ≤ Submodule.span K {e 0, e 1, e 2} :=
    Submodule.span_mono (Set.insert_subset_insert (by simp))
  ext T'
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hHT, hT'3, hT'iso, hT'ne⟩
    obtain ⟨m, hmT, hmH⟩ := IsConcreteLE.exists_of_lt hHT
    have he0T : e 0 ∈ T' := hHT.le (Submodule.subset_span (by simp))
    have he1T : e 1 ∈ T' := hHT.le (Submodule.subset_span (by simp))
    have hexp := eq_sum_frame h hB hBl hV he hf hef m
    rw [Fin.sum_univ_three, hT'iso _ he0T _ hmT, hT'iso _ he1T _ hmT, zero_smul, zero_smul,
      add_zero, add_zero] at hexp
    obtain ⟨c₀, hc₀⟩ : ∃ c, c = B (f 0) m := ⟨_, rfl⟩
    obtain ⟨c₁, hc₁⟩ : ∃ c, c = B (f 1) m := ⟨_, rfl⟩
    obtain ⟨c₂, hc₂⟩ : ∃ c, c = B (f 2) m := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ c, c = B (e 2) m := ⟨_, rfl⟩
    rw [← hc₀, ← hc₁, ← hc₂, ← hd] at hexp
    have hx₀ : c₂ • e 2 + d • f 2 ∈ T' := by
      have : c₂ • e 2 + d • f 2 = m - c₀ • e 0 - c₁ • e 1 := by
        rw [hexp]
        abel
      rw [this]
      exact T'.sub_mem (T'.sub_mem hmT (T'.smul_mem _ he0T)) (T'.smul_mem _ he1T)
    have hiso : h.bar c₂ * d + h.bar d * c₂ = 0 := by
      have := hT'iso _ hx₀ _ hx₀
      simp [he, hf, hef, hfe] at this
      linear_combination this
    by_cases hd0 : d = 0
    · exfalso
      apply hT'ne
      have hmT₀ : m ∈ Submodule.span K {e 0, e 1, e 2} := by
        rw [hexp, hd0, zero_smul, add_zero]
        exact Submodule.add_mem _ (Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      have hsup := sup_span_singleton_eq hHT.le (by rw [hT'3, hH2]) hmT hmH
      refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hT'3, hT3])
      rw [← hsup]
      exact sup_le hHT₀ ((Submodule.span_singleton_le_iff_mem _ _).2 hmT₀)
    · have hbd : h.bar d ≠ 0 := (map_ne_zero h.bar).2 hd0
      have hμ : c₂ * d⁻¹ + h.bar (c₂ * d⁻¹) = 0 := by
        rw [map_mul, map_inv₀]
        field_simp
        linear_combination hiso
      have hx₁ : (c₂ * d⁻¹) • e 2 + f 2 ∈ T' := by
        have : (c₂ * d⁻¹) • e 2 + f 2 = d⁻¹ • (c₂ • e 2 + d • f 2) := by
          rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hd0, one_smul, mul_comm]
        rw [this]
        exact T'.smul_mem _ hx₀
      rcases eq_zero_or_eq_one_of_trace h _ hμ with hμ0 | hμ1
      · left
        rw [hμ0, zero_smul, zero_add] at hx₁
        refine (Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hT₁3, hT'3])).symm
        rw [Submodule.span_le]
        rintro _ (rfl | rfl | rfl)
        exacts [he0T, he1T, hx₁]
      · right
        rw [hμ1, one_smul] at hx₁
        refine (Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hT₂3, hT'3])).symm
        rw [Submodule.span_le]
        rintro _ (rfl | rfl | rfl)
        exacts [he0T, he1T, hx₁]
  · have he2T₀ : e 2 ∈ Submodule.span K {e 0, e 1, e 2} := Submodule.subset_span (by simp)
    rintro (rfl | rfl)
    · refine ⟨lt_of_le_of_ne (Submodule.span_mono (Set.insert_subset_insert (by simp))) ?_,
        hT₁3, (isotropic_panelT h hB he hf hef).1, ?_⟩
      · intro hEq
        have hmem : f 2 ∈ Submodule.span K {e 0, e 1} := by
          rw [hEq]
          exact Submodule.subset_span (by simp)
        have := hiso₀ _ he2T₀ _ (hHT₀ hmem)
        simp [hef] at this
      · intro hEq
        have hmem : f 2 ∈ Submodule.span K {e 0, e 1, e 2} := by
          rw [← hEq]
          exact Submodule.subset_span (by simp)
        have := hiso₀ _ he2T₀ _ hmem
        simp [hef] at this
    · refine ⟨lt_of_le_of_ne (Submodule.span_mono (Set.insert_subset_insert (by simp))) ?_,
        hT₂3, (isotropic_panelT h hB he hf hef).2, ?_⟩
      · intro hEq
        have hmem : e 2 + f 2 ∈ Submodule.span K {e 0, e 1} := by
          rw [hEq]
          exact Submodule.subset_span (by simp)
        have := hiso₀ _ he2T₀ _ (hHT₀ hmem)
        simp [he, hef] at this
      · intro hEq
        have hmem : e 2 + f 2 ∈ Submodule.span K {e 0, e 1, e 2} := by
          rw [← hEq]
          exact Submodule.subset_span (by simp)
        have := hiso₀ _ he2T₀ _ hmem
        simp [he, hef] at this

include he hf in
theorem exists_SU_panelR (a b : K) :
    ∃ g ∈ sesqSpecialUnitaryGroup B,
      (Submodule.span K {e 0}).map (g : V →ₗ[K] V) = Submodule.span K {e 0} ∧
      (Submodule.span K {e 0, e 1}).map (g : V →ₗ[K] V) = Submodule.span K {e 0, e 1} ∧
      (Submodule.span K {e 0, e 1, e 2}).map (g : V →ₗ[K] V) =
        Submodule.span K {e 0, e 1, e 2} ∧
      (Submodule.span K {e 1 + a • e 0}).map (g : V →ₗ[K] V) =
        Submodule.span K {e 1 + b • e 0} := by
  have hfe := frame_fe h hB hef
  have hey : B (e 0) (h.bar (a - b) • f 1) = 0 := by simp [hef]
  have hye : B (h.bar (a - b) • f 1) (e 0) = 0 := by simp [hfe]
  have hyy : B (h.bar (a - b) • f 1) (h.bar (a - b) • f 1) = 0 := by simp [hf]
  obtain ⟨g, hg, hgφ⟩ := exists_mem_sesqSpecialUnitaryGroup
    (eichlerMap_isometry hB (he 0 0) hey (by rw [hyy, map_zero, add_zero, add_zero]))
    (det_eichlerMap (he 0 0) hey hye 0)
  have hg0 : (g : V →ₗ[K] V) (e 0) = e 0 := by
    rw [hgφ, eichlerMap_apply]
    simp [he, hfe]
  have hg1 : (g : V →ₗ[K] V) (e 1) = e 1 - (a - b) • e 0 := by
    rw [hgφ, eichlerMap_apply]
    simp [he, hfe, h.bar_bar]
  have hg2 : (g : V →ₗ[K] V) (e 2) = e 2 := by
    rw [hgφ, eichlerMap_apply]
    simp [he, hfe]
  obtain ⟨h0, h1, h2⟩ := map_flag_eq g
    (by rw [hg0]; exact Submodule.mem_span_singleton_self _)
    (by
      rw [hg1]
      exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
    (by rw [hg2]; exact Submodule.subset_span (by simp))
  refine ⟨g, hg, h0, h1, h2, ?_⟩
  have hv : (g : V →ₗ[K] V) (e 1 + a • e 0) = e 1 + b • e 0 := by
    rw [map_add, map_smul, hg0, hg1]
    module
  rw [Submodule.map_span, Set.image_singleton, hv]

include he hf in
theorem exists_SU_panelH (a b : K) :
    ∃ g ∈ sesqSpecialUnitaryGroup B,
      (Submodule.span K {e 0}).map (g : V →ₗ[K] V) = Submodule.span K {e 0} ∧
      (Submodule.span K {e 0, e 1}).map (g : V →ₗ[K] V) = Submodule.span K {e 0, e 1} ∧
      (Submodule.span K {e 0, e 1, e 2}).map (g : V →ₗ[K] V) =
        Submodule.span K {e 0, e 1, e 2} ∧
      (Submodule.span K {e 0, e 2 + a • e 1}).map (g : V →ₗ[K] V) =
        Submodule.span K {e 0, e 2 + b • e 1} := by
  have hfe := frame_fe h hB hef
  have hey : B (e 1) (h.bar (a - b) • f 2) = 0 := by simp [hef]
  have hye : B (h.bar (a - b) • f 2) (e 1) = 0 := by simp [hfe]
  have hyy : B (h.bar (a - b) • f 2) (h.bar (a - b) • f 2) = 0 := by simp [hf]
  obtain ⟨g, hg, hgφ⟩ := exists_mem_sesqSpecialUnitaryGroup
    (eichlerMap_isometry hB (he 1 1) hey (by rw [hyy, map_zero, add_zero, add_zero]))
    (det_eichlerMap (he 1 1) hey hye 0)
  have hg0 : (g : V →ₗ[K] V) (e 0) = e 0 := by
    rw [hgφ, eichlerMap_apply]
    simp [he, hfe]
  have hg1 : (g : V →ₗ[K] V) (e 1) = e 1 := by
    rw [hgφ, eichlerMap_apply]
    simp [he, hfe]
  have hg2 : (g : V →ₗ[K] V) (e 2) = e 2 - (a - b) • e 1 := by
    rw [hgφ, eichlerMap_apply]
    simp [he, hfe, h.bar_bar]
  obtain ⟨h0, h1, h2⟩ := map_flag_eq g
    (by rw [hg0]; exact Submodule.mem_span_singleton_self _)
    (by rw [hg1]; exact Submodule.subset_span (by simp))
    (by
      rw [hg2]
      exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  refine ⟨g, hg, h0, h1, h2, ?_⟩
  have hv : (g : V →ₗ[K] V) (e 2 + a • e 1) = e 2 + b • e 1 := by
    rw [map_add, map_smul, hg1, hg2]
    module
  rw [Submodule.map_span, Set.image_pair, hg0, hv]

include he in
theorem exists_SU_panelT :
    ∃ g ∈ sesqSpecialUnitaryGroup B,
      (Submodule.span K {e 0}).map (g : V →ₗ[K] V) = Submodule.span K {e 0} ∧
      (Submodule.span K {e 0, e 1}).map (g : V →ₗ[K] V) = Submodule.span K {e 0, e 1} ∧
      (Submodule.span K {e 0, e 1, e 2}).map (g : V →ₗ[K] V) =
        Submodule.span K {e 0, e 1, e 2} ∧
      (Submodule.span K {e 0, e 1, f 2}).map (g : V →ₗ[K] V) =
        Submodule.span K {e 0, e 1, e 2 + f 2} ∧
      (Submodule.span K {e 0, e 1, e 2 + f 2}).map (g : V →ₗ[K] V) =
        Submodule.span K {e 0, e 1, f 2} := by
  refine ⟨hermTransvectionGL B (he 2 2) 1,
    (hermitian_unitary_transvection h hB (he 2 2)).2.1 1 (one_mem_traceZero h), ?_⟩
  have happ : ∀ x, ((hermTransvectionGL B (he 2 2) 1 : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) x = x + B (e 2) x • e 2 := fun x => by
    rw [coe_hermTransvectionGL, hermTransvection_apply, one_mul]
  have hg0 := happ (e 0)
  have hg1 := happ (e 1)
  have hg2 := happ (e 2)
  have hgf := happ (f 2)
  rw [he, zero_smul, add_zero] at hg0 hg1 hg2
  rw [hef] at hgf
  simp only [↓reduceIte, one_smul] at hgf
  have hgef : ((hermTransvectionGL B (he 2 2) 1 : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) (e 2 + f 2) = f 2 := by
    rw [map_add, hg2, hgf, add_comm (f 2), ← add_assoc, add_self_eq_zero_V h, zero_add]
  obtain ⟨h0, h1, h2⟩ := map_flag_eq (hermTransvectionGL B (he 2 2) 1)
    (by rw [hg0]; exact Submodule.mem_span_singleton_self _)
    (by rw [hg1]; exact Submodule.subset_span (by simp))
    (by rw [hg2]; exact Submodule.subset_span (by simp))
  refine ⟨h0, h1, h2, ?_, ?_⟩
  · rw [Submodule.map_span, Set.image_insert_eq, Set.image_pair, hg0, hg1, hgf, add_comm]
  · rw [Submodule.map_span, Set.image_insert_eq, Set.image_pair, hg0, hg1, hgef]

end Panels

theorem unitary_six_derived_flag_panel_actions (h : UnitaryFieldData 2 1 K)
    [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (hV : finrank K V = 6) {R H T : Submodule K V} (hRH : R < H)
    (hHT : H < T) (hR : finrank K R = 1) (hH : finrank K H = 2) (hT : finrank K T = 3)
    (hTi : ∀ x ∈ T, ∀ y ∈ T, B x y = 0) :
    (∀ z ∈ Subgroup.center (sesqSpecialUnitaryGroup B), ∀ W : Submodule K V,
        W.map ((z : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = W) ∧
    ({R' : Submodule K V | finrank K R' = 1 ∧ R' < H ∧ R' ≠ R}.ncard = 4 ∧
      (∀ u ∈ psuFlagStabilizer h hB hBl hV R H T,
        ∀ X ∈ {R' : Submodule K V | finrank K R' = 1 ∧ R' < H ∧ R' ≠ R},
          psuSubspaceAction h hB hBl hV u X ∈
            {R' : Submodule K V | finrank K R' = 1 ∧ R' < H ∧ R' ≠ R}) ∧
      ∀ X ∈ {R' : Submodule K V | finrank K R' = 1 ∧ R' < H ∧ R' ≠ R},
        ∀ Y ∈ {R' : Submodule K V | finrank K R' = 1 ∧ R' < H ∧ R' ≠ R},
          ∃ u ∈ psuFlagStabilizer h hB hBl hV R H T, psuSubspaceAction h hB hBl hV u X = Y) ∧
    ({H' : Submodule K V | R < H' ∧ H' < T ∧ finrank K H' = 2 ∧ H' ≠ H}.ncard = 4 ∧
      (∀ u ∈ psuFlagStabilizer h hB hBl hV R H T,
        ∀ X ∈ {H' : Submodule K V | R < H' ∧ H' < T ∧ finrank K H' = 2 ∧ H' ≠ H},
          psuSubspaceAction h hB hBl hV u X ∈
            {H' : Submodule K V | R < H' ∧ H' < T ∧ finrank K H' = 2 ∧ H' ≠ H}) ∧
      ∀ X ∈ {H' : Submodule K V | R < H' ∧ H' < T ∧ finrank K H' = 2 ∧ H' ≠ H},
        ∀ Y ∈ {H' : Submodule K V | R < H' ∧ H' < T ∧ finrank K H' = 2 ∧ H' ≠ H},
          ∃ u ∈ psuFlagStabilizer h hB hBl hV R H T, psuSubspaceAction h hB hBl hV u X = Y) ∧
    ({T' : Submodule K V | H < T' ∧ finrank K T' = 3 ∧ (∀ x ∈ T', ∀ y ∈ T', B x y = 0) ∧
        T' ≠ T}.ncard = 2 ∧
      (∀ u ∈ psuFlagStabilizer h hB hBl hV R H T,
        ∀ X ∈ {T' : Submodule K V | H < T' ∧ finrank K T' = 3 ∧
          (∀ x ∈ T', ∀ y ∈ T', B x y = 0) ∧ T' ≠ T},
          psuSubspaceAction h hB hBl hV u X ∈ {T' : Submodule K V | H < T' ∧ finrank K T' = 3 ∧
            (∀ x ∈ T', ∀ y ∈ T', B x y = 0) ∧ T' ≠ T}) ∧
      ∀ X ∈ {T' : Submodule K V | H < T' ∧ finrank K T' = 3 ∧
          (∀ x ∈ T', ∀ y ∈ T', B x y = 0) ∧ T' ≠ T},
        ∀ Y ∈ {T' : Submodule K V | H < T' ∧ finrank K T' = 3 ∧
          (∀ x ∈ T', ∀ y ∈ T', B x y = 0) ∧ T' ≠ T},
          ∃ u ∈ psuFlagStabilizer h hB hBl hV R H T, psuSubspaceAction h hB hBl hV u X = Y) := by
  refine ⟨fun z hz W => ?_, ?_⟩
  · have := center_le_ker_toPermHom h hB hBl hV hz
    rw [MonoidHom.mem_ker] at this
    exact congrArg (fun π : Equiv.Perm (Submodule K V) => π W) this
  obtain ⟨e, f, he, hf, hef, rfl, rfl, rfl⟩ :=
    exists_frame_of_flag h hB hBl hRH hHT hR hH hT hTi
  refine ⟨⟨?_, fun u hu X hX => mapsTo_panelR h hB hBl hV hu hX, ?_⟩,
    ⟨?_, fun u hu X hX => mapsTo_panelH h hB hBl hV hu hX, ?_⟩,
    ⟨?_, fun u hu X hX => mapsTo_panelT h hB hBl hV hu hX, ?_⟩⟩
  · rw [panelR_eq h hB hef, Set.ncard_range_of_injective (panelR_injective h hB hef),
      card_eq_four h]
  · rw [panelR_eq h hB hef]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    obtain ⟨g, hg, h0, h1, h2, hab⟩ := exists_SU_panelR h hB he hf hef a b
    exact exists_mem_psuFlagStabilizer h hB hBl hV hg h0 h1 h2 hab
  · rw [panelH_eq h hB hef, Set.ncard_range_of_injective (panelH_injective h hB hef),
      card_eq_four h]
  · rw [panelH_eq h hB hef]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    obtain ⟨g, hg, h0, h1, h2, hab⟩ := exists_SU_panelH h hB he hf hef a b
    exact exists_mem_psuFlagStabilizer h hB hBl hV hg h0 h1 h2 hab
  · rw [panelT_eq h hB he hf hef hBl hV]
    exact Set.ncard_pair (panelT_ne h hB he hf hef)
  · rw [panelT_eq h hB he hf hef hBl hV]
    obtain ⟨g, hg, h0, h1, h2, h12, h21⟩ := exists_SU_panelT h hB he hef
    have hone : ∀ X : Submodule K V, ∃ u ∈ psuFlagStabilizer h hB hBl hV
        (Submodule.span K {e 0}) (Submodule.span K {e 0, e 1})
        (Submodule.span K {e 0, e 1, e 2}), psuSubspaceAction h hB hBl hV u X = X :=
      fun X => ⟨1, one_mem _, by rw [map_one]; rfl⟩
    rintro X (rfl | rfl) Y (rfl | rfl)
    · exact hone _
    · exact exists_mem_psuFlagStabilizer h hB hBl hV hg h0 h1 h2 h12
    · exact exists_mem_psuFlagStabilizer h hB hBl hV hg h0 h1 h2 h21
    · exact hone _

end CFSG.Monster.B.Classical.UnitaryPanels

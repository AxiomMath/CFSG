module

public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryPairing
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.RankThree.PartOne.KCUnitary

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary

section Centralizer

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {x : LinearMap.GeneralLinearGroup K V}

abbrev gl_centralizer (x : LinearMap.GeneralLinearGroup K V) :
    Subgroup (LinearMap.GeneralLinearGroup K V) := Subgroup.centralizer {x}

omit [FiniteDimensional K V] in
theorem mem_gl_centralizer {g : LinearMap.GeneralLinearGroup K V} :
    g ∈ gl_centralizer x ↔ Commute (g : Module.End K V) (x : Module.End K V) := by
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [commute_iff_eq, eq_comm, ← Units.val_mul, ← Units.val_mul]
  exact ⟨fun h => by rw [h], fun h => Units.ext h⟩

omit [FiniteDimensional K V] in
theorem mem_commutant_of_mem_gl_centralizer {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ gl_centralizer x) : (g : Module.End K V) ∈ commutant (x : Module.End K V) :=
  (mem_commutant _).mpr (mem_gl_centralizer.mp hg)


@[expose] noncomputable def glCentralizerEquivUnits (x : LinearMap.GeneralLinearGroup K V) :
    gl_centralizer x ≃* (commutant (x : Module.End K V))ˣ where
  toFun g := ⟨⟨(g : LinearMap.GeneralLinearGroup K V),
      mem_commutant_of_mem_gl_centralizer g.2⟩,
    ⟨((g⁻¹ : gl_centralizer x) : LinearMap.GeneralLinearGroup K V),
      mem_commutant_of_mem_gl_centralizer (g⁻¹).2⟩,
    Subtype.ext (by simp [← Units.val_mul]), Subtype.ext (by simp [← Units.val_mul])⟩
  invFun u := ⟨⟨(u : commutant (x : Module.End K V)).1, ((u⁻¹ : (commutant
      (x : Module.End K V))ˣ) : commutant (x : Module.End K V)).1,
      congrArg Subtype.val u.mul_inv, congrArg Subtype.val u.inv_mul⟩,
    mem_gl_centralizer.mpr ((mem_commutant _).mp (u : commutant (x : Module.End K V)).2)⟩
  left_inv g := Subtype.ext (Units.ext rfl)
  right_inv u := Units.ext (Subtype.ext rfl)
  map_mul' g h := Units.ext (Subtype.ext rfl)


abbrev blockGL (X : Module.End K V) (b : K[X]) : Type _ :=
  LinearMap.GeneralLinearGroup (AdjoinRoot b) (primaryComponent X b)

@[expose] def blockApply {X : Module.End K V} {b : K[X]} (γ : blockGL X b) (v : V)
    (hv : v ∈ primaryComponent X b) : V :=
  ((γ : Module.End (AdjoinRoot b) (primaryComponent X b)) ⟨v, hv⟩ : primaryComponent X b)

omit [FiniteDimensional K V] in
theorem blockApply_mem {X : Module.End K V} {b : K[X]} (γ : blockGL X b) (v : V)
    (hv : v ∈ primaryComponent X b) : blockApply γ v hv ∈ primaryComponent X b :=
  ((γ : Module.End (AdjoinRoot b) (primaryComponent X b)) ⟨v, hv⟩).2

omit [FiniteDimensional K V] in
theorem blockApply_blockApply {X : Module.End K V} {b : K[X]} (γ γ' : blockGL X b) (v : V)
    (hv : v ∈ primaryComponent X b) :
    blockApply γ (blockApply γ' v hv) (blockApply_mem γ' v hv) = blockApply (γ * γ') v hv := rfl

omit [FiniteDimensional K V] in
theorem blockApply_one {X : Module.End K V} {b : K[X]} (v : V) (hv : v ∈ primaryComponent X b) :
    blockApply (1 : blockGL X b) v hv = v := rfl

@[expose] noncomputable def glCentralizerEquivPi
    (hsq : Squarefree (minpoly K (x : Module.End K V))) :
    gl_centralizer x ≃* ((b : primaryFactors (x : Module.End K V)) →
      blockGL (x : Module.End K V) (b : K[X])) :=
  (glCentralizerEquivUnits x).trans (commutantUnitsEquivPi hsq)

theorem blockApply_glCentralizerEquivPi (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (g : gl_centralizer x) (b : primaryFactors (x : Module.End K V)) (v : V)
    (hv : v ∈ primaryComponent (x : Module.End K V) (b : K[X])) :
    blockApply (glCentralizerEquivPi hsq g b) v hv =
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v := rfl

section Unitary

variable {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K}

@[expose] def unitaryCentralizer (B : V →ₛₗ[σ] V →ₗ[K] K) (x : LinearMap.GeneralLinearGroup K V) :
    Subgroup (LinearMap.GeneralLinearGroup K V) :=
  sesqUnitaryGroup B ⊓ gl_centralizer x

omit [FiniteDimensional K V] in
theorem mem_unitaryCentralizer {g : LinearMap.GeneralLinearGroup K V} :
    g ∈ unitaryCentralizer B x ↔ g ∈ sesqUnitaryGroup B ∧
      Commute (g : Module.End K V) (x : Module.End K V) := by
  rw [unitaryCentralizer, Subgroup.mem_inf, mem_gl_centralizer]

variable (H : UnitaryPrimaryData σ B x)
include H

theorem mem_unitaryCentralizer_iff_blocks {g : LinearMap.GeneralLinearGroup K V} :
    g ∈ unitaryCentralizer B x ↔ Commute (g : Module.End K V) (x : Module.End K V) ∧
      ∀ b ∈ primaryFactors (x : Module.End K V),
        ∀ v ∈ primaryComponent (x : Module.End K V) b,
        ∀ w ∈ primaryComponent (x : Module.End K V) (dualPoly σ b),
          B ((g : Module.End K V) v) ((g : Module.End K V) w) = B v w := by
  rw [mem_unitaryCentralizer]
  constructor
  · rintro ⟨hg, hc⟩
    exact ⟨hc, fun b _ v _ w _ => hg v w⟩
  · rintro ⟨hc, h⟩
    refine ⟨fun v w => ?_, hc⟩
    have hsq := H.squarefree
    have hπ : ∀ b, Commute (g : Module.End K V)
        (primaryProjection (x : Module.End K V) b) := fun b =>
      commute_aeval hc _
    rw [B_eq_sum H ((g : Module.End K V) v) ((g : Module.End K V) w), B_eq_sum H v w]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hπ1 : ∀ c (u : V), primaryProjection (x : Module.End K V) c ((g : Module.End K V) u) =
        (g : Module.End K V) (primaryProjection (x : Module.End K V) c u) := fun c u =>
      (congrArg (fun T : Module.End K V => T u) (hπ c).eq).symm
    rw [hπ1, hπ1]
    exact h b hb _ (primaryProjection_mem hsq hb v) _
      (primaryProjection_mem hsq (dualPoly_mem_primaryFactors H hb) w)


@[expose] noncomputable def dualFactor (b : primaryFactors (x : Module.End K V)) :
    primaryFactors (x : Module.End K V) :=
  ⟨dualPoly σ (b : K[X]), dualPoly_mem_primaryFactors H b.2⟩

omit H in
@[expose] def supportedUnitary (B : V →ₛₗ[σ] V →ₗ[K] K) (x : LinearMap.GeneralLinearGroup K V)
    (S : Set K[X]) : Subgroup (LinearMap.GeneralLinearGroup K V) where
  carrier := {g | g ∈ unitaryCentralizer B x ∧ ∀ b ∈ primaryFactors (x : Module.End K V), b ∉ S →
    ∀ v ∈ primaryComponent (x : Module.End K V) b, (g : Module.End K V) v = v}
  mul_mem' {g g'} hg hg' := by
    refine ⟨(unitaryCentralizer B x).mul_mem hg.1 hg'.1, fun b hb hbS v hv => ?_⟩
    rw [Units.val_mul, Module.End.mul_apply, hg'.2 b hb hbS v hv, hg.2 b hb hbS v hv]
  one_mem' := ⟨(unitaryCentralizer B x).one_mem, fun _ _ _ _ _ => rfl⟩
  inv_mem' {g} hg := by
    refine ⟨(unitaryCentralizer B x).inv_mem hg.1, fun b hb hbS v hv => ?_⟩
    have h1 := hg.2 b hb hbS v hv
    calc ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v
        = ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
          ((g : Module.End K V) v) := by rw [h1]
      _ = v := by
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]; rfl

omit [FiniteDimensional K V] H in
theorem supportedUnitary_le_unitaryCentralizer (S : Set K[X]) :
    supportedUnitary B x S ≤ unitaryCentralizer B x := fun _ hg => hg.1

omit [FiniteDimensional K V] H in
theorem supportedUnitary_le_gl_centralizer (S : Set K[X]) :
    supportedUnitary B x S ≤ gl_centralizer x := fun _ hg => hg.1.2


theorem adj_commute {r : Module.End K V} (hr : Commute r (x : Module.End K V)) :
    Commute (H.adj r) (x : Module.End K V) := by
  set X : Module.End K V := (x : Module.End K V) with hX
  set Y : Module.End K V := ((x⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) with hY
  have hXY : X * Y = 1 := by rw [hX, hY, ← Units.val_mul, mul_inv_cancel]; rfl
  have hYX : Y * X = 1 := by rw [hX, hY, ← Units.val_mul, inv_mul_cancel]; rfl
  have hadjX : H.adj X = Y := hermAdjoint_of_mem_sesqUnitaryGroup H.symm H.sep H.isom
  have h1 : H.adj (r * X) = H.adj (X * r) := by rw [hr.eq]
  rw [UnitaryPrimaryData.adj, UnitaryPrimaryData.adj] at h1
  rw [hermAdjoint_mul, hermAdjoint_mul] at h1
  change H.adj X * H.adj r = H.adj r * H.adj X at h1
  rw [hadjX] at h1
  rw [Commute, SemiconjBy]
  calc H.adj r * X = X * (Y * H.adj r) * X := by rw [← mul_assoc, hXY, one_mul]
    _ = X * (H.adj r * Y) * X := by rw [h1]
    _ = X * H.adj r := by
      rw [mul_assoc, mul_assoc, hYX, mul_one]

@[expose] noncomputable def adjUnit (g : LinearMap.GeneralLinearGroup K V) :
    LinearMap.GeneralLinearGroup K V :=
  ⟨H.adj (g : Module.End K V), H.adj ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V),
    by
      rw [UnitaryPrimaryData.adj, UnitaryPrimaryData.adj, ← hermAdjoint_mul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, hermAdjoint_one],
    by
      rw [UnitaryPrimaryData.adj, UnitaryPrimaryData.adj, ← hermAdjoint_mul, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, hermAdjoint_one]⟩

theorem coe_adjUnit (g : LinearMap.GeneralLinearGroup K V) :
    ((adjUnit H g : LinearMap.GeneralLinearGroup K V) : Module.End K V) =
      H.adj (g : Module.End K V) := rfl

theorem adjUnit_mem_gl_centralizer {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ gl_centralizer x) : adjUnit H g ∈ gl_centralizer x :=
  mem_gl_centralizer.mpr (adj_commute H (mem_gl_centralizer.mp hg))


@[expose] noncomputable def supportedRestrict (S : Set K[X])
    (a : primaryFactors (x : Module.End K V)) :
    supportedUnitary B x S →* blockGL (x : Module.End K V) (a : K[X]) :=
  (Pi.evalMonoidHom (fun b : primaryFactors (x : Module.End K V) =>
      blockGL (x : Module.End K V) (b : K[X])) a).comp
    ((glCentralizerEquivPi H.squarefree).toMonoidHom.comp
      (Subgroup.inclusion (supportedUnitary_le_gl_centralizer S)))

theorem coe_supportedRestrict (S : Set K[X]) (a : primaryFactors (x : Module.End K V))
    (g : supportedUnitary B x S) (v : primaryComponent (x : Module.End K V) (a : K[X])) :
    ((((supportedRestrict H S a g : blockGL (x : Module.End K V) (a : K[X])) :
      Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) v :
      primaryComponent (x : Module.End K V) (a : K[X])) : V) =
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) (v : V) := rfl

theorem eq_one_of_paired {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ supportedUnitary B x {a, dualPoly σ a})
    (h1 : ∀ v ∈ primaryComponent (x : Module.End K V) a, (g : Module.End K V) v = v) :
    g = 1 := by
  have hsq := H.squarefree
  have hb := dualPoly_mem_primaryFactors H ha
  have hcomm := (mem_unitaryCentralizer.mp hg.1)
  refine Units.ext (ext_primaryComponent hsq fun c hc v hv => ?_)
  by_cases hca : c = a
  · subst hca; exact h1 v hv
  by_cases hcb : c = dualPoly σ a
  · subst hcb
    have hgw : (g : Module.End K V) v - v ∈
        primaryComponent (x : Module.End K V) (dualPoly σ a) :=
      Submodule.sub_mem _ (apply_mem_primaryComponent hcomm.2 hv) hv
    have hzero := eq_zero_of_perfect_right H ha hb rfl hgw fun u hu => by
      have e1 : B u ((g : Module.End K V) v) = B u v := by
        have := hcomm.1 u v
        rw [h1 u hu] at this
        exact this
      rw [map_sub, e1, sub_self]
    exact (sub_eq_zero.mp hzero)
  · exact hg.2 c hc (by simp [hca, hcb]) v hv


theorem glue_apply (Γ : (b : primaryFactors (x : Module.End K V)) →
      blockGL (x : Module.End K V) (b : K[X]))
    (i : primaryFactors (x : Module.End K V)) {v : V}
    (hv : v ∈ primaryComponent (x : Module.End K V) (i : K[X])) :
    ((((glCentralizerEquivPi H.squarefree).symm Γ : gl_centralizer x) :
        LinearMap.GeneralLinearGroup K V) : Module.End K V) v = blockApply (Γ i) v hv := by
  have h := blockApply_glCentralizerEquivPi H.squarefree
    ((glCentralizerEquivPi H.squarefree).symm Γ) i v hv
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem exists_inverse_adjoint_block {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    (γ : blockGL (x : Module.End K V) a) :
    ∃ δ : blockGL (x : Module.End K V) (dualPoly σ a),
      ∀ (v w : V) (hv : v ∈ primaryComponent (x : Module.End K V) a)
        (hw : w ∈ primaryComponent (x : Module.End K V) (dualPoly σ a)),
        B (blockApply γ v hv) (blockApply δ w hw) = B v w := by
  classical
  have hsq := H.squarefree
  have hb := dualPoly_mem_primaryFactors H ha
  let ia : primaryFactors (x : Module.End K V) := ⟨a, ha⟩
  let ib : primaryFactors (x : Module.End K V) := ⟨dualPoly σ a, hb⟩
  let Γ₀ : (b : primaryFactors (x : Module.End K V)) → blockGL (x : Module.End K V) (b : K[X]) :=
    Function.update 1 ia γ
  let g₀ : gl_centralizer x := (glCentralizerEquivPi hsq).symm Γ₀
  have hg₀ : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) a),
      ((g₀ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = blockApply γ v hv :=
    fun v hv => by
      rw [glue_apply H Γ₀ ia hv]
      simp [Γ₀, ia]
  let ũ : gl_centralizer x := ⟨adjUnit H g₀, adjUnit_mem_gl_centralizer H g₀.2⟩
  refine ⟨(glCentralizerEquivPi hsq ũ ib)⁻¹, fun v w hv hw => ?_⟩
  have h1 : blockApply γ v hv = ((g₀ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v :=
    (hg₀ v hv).symm
  have h2 : blockApply (glCentralizerEquivPi hsq ũ ib)
      (blockApply (glCentralizerEquivPi hsq ũ ib)⁻¹ w hw) (blockApply_mem _ w hw) = w := by
    rw [blockApply_blockApply, mul_inv_cancel, blockApply_one]
  have h3 := (blockApply_glCentralizerEquivPi hsq ũ ib
    (blockApply (glCentralizerEquivPi hsq ũ ib)⁻¹ w hw) (blockApply_mem _ w hw)).symm.trans h2
  calc B (blockApply γ v hv) (blockApply (glCentralizerEquivPi hsq ũ ib)⁻¹ w hw)
      = B (((g₀ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)
        (blockApply (glCentralizerEquivPi hsq ũ ib)⁻¹ w hw) := by rw [h1]
    _ = B v (H.adj ((g₀ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
        (blockApply (glCentralizerEquivPi hsq ũ ib)⁻¹ w hw)) := H.adj_spec _ _ _
    _ = B v w := by rw [show H.adj ((g₀ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
        (blockApply (glCentralizerEquivPi hsq ũ ib)⁻¹ w hw) = w from h3]


theorem supportedRestrict_surjective_of_paired {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) (hne : a ≠ dualPoly σ a) :
    Function.Surjective (supportedRestrict H {a, dualPoly σ a} ⟨a, ha⟩) := by
  classical
  intro γ
  have hsq := H.squarefree
  have hb := dualPoly_mem_primaryFactors H ha
  obtain ⟨δ, hδ⟩ := exists_inverse_adjoint_block H ha γ
  let ia : primaryFactors (x : Module.End K V) := ⟨a, ha⟩
  let ib : primaryFactors (x : Module.End K V) := ⟨dualPoly σ a, hb⟩
  have hiab : ia ≠ ib := fun h => hne (congrArg Subtype.val h)
  let Γ : (b : primaryFactors (x : Module.End K V)) → blockGL (x : Module.End K V) (b : K[X]) :=
    Function.update (Function.update 1 ia γ) ib δ
  let g : gl_centralizer x := (glCentralizerEquivPi hsq).symm Γ
  have hΓa : Γ ia = γ := by simp [Γ, hiab]
  have hΓb : Γ ib = δ := by simp [Γ]
  have hΓo : ∀ i, i ≠ ia → i ≠ ib → Γ i = 1 := fun i h1 h2 => by simp [Γ, h1, h2]
  have hga : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) a),
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = blockApply γ v hv :=
    fun v hv => by rw [glue_apply H Γ ia hv, hΓa]
  have hgb : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) (dualPoly σ a)),
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = blockApply δ v hv :=
    fun v hv => by rw [glue_apply H Γ ib hv, hΓb]
  have hgo : ∀ c ∈ primaryFactors (x : Module.End K V), c ≠ a → c ≠ dualPoly σ a →
      ∀ v ∈ primaryComponent (x : Module.End K V) c,
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
    intro c hc hca hcb v hv
    rw [glue_apply H Γ ⟨c, hc⟩ hv, hΓo ⟨c, hc⟩ (fun h => hca (congrArg Subtype.val h))
      (fun h => hcb (congrArg Subtype.val h)), blockApply_one]
  have hmem : (g : LinearMap.GeneralLinearGroup K V) ∈ supportedUnitary B x {a, dualPoly σ a} := by
    refine ⟨(mem_unitaryCentralizer_iff_blocks H).mpr ⟨mem_gl_centralizer.mp g.2, ?_⟩, ?_⟩
    · intro c hc v hv w hw
      by_cases hca : c = a
      · subst hca
        rw [hga v hv, hgb w hw]
        exact hδ v w hv hw
      by_cases hcb : c = dualPoly σ a
      · subst hcb
        have hw' : w ∈ primaryComponent (x : Module.End K V) a := by
          rwa [dualPoly_dualPoly_of_mem H ha] at hw
        rw [hgb v hv, hga w hw']
        have h1 := hδ w v hw' hv
        have h2 := (H.symm.eq (blockApply γ w hw') (blockApply δ v hv))
        have h3 := (H.symm.eq w v)
        rw [h1] at h2
        rw [← h2, h3]
      · have hc1 : dualPoly σ c ≠ a := fun h => hcb (by
          rw [← h, dualPoly_dualPoly_of_mem H hc])
        have hc2 : dualPoly σ c ≠ dualPoly σ a := fun h => hca (dualPoly_injOn H hc ha h)
        rw [hgo c hc hca hcb v hv,
          hgo (dualPoly σ c) (dualPoly_mem_primaryFactors H hc) hc1 hc2 w hw]
    · intro c hc hcS v hv
      exact hgo c hc (fun h => hcS (Or.inl h)) (fun h => hcS (Or.inr h)) v hv
  refine ⟨⟨(g : LinearMap.GeneralLinearGroup K V), hmem⟩, ?_⟩
  apply Units.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact hga v v.2


theorem supportedRestrict_injective_of_paired {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) :
    Function.Injective (supportedRestrict H {a, dualPoly σ a} ⟨a, ha⟩) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  refine eq_one_of_paired H ha g.2 fun v hv => ?_
  have h1 := congrArg (fun γ : blockGL (x : Module.End K V) a =>
    ((γ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) ⟨v, hv⟩ :
      primaryComponent (x : Module.End K V) a)) hg
  exact congrArg Subtype.val h1

@[expose] noncomputable def pairedFactorEquiv {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) (hne : a ≠ dualPoly σ a) :
    supportedUnitary B x {a, dualPoly σ a} ≃* blockGL (x : Module.End K V) a :=
  MulEquiv.ofBijective (supportedRestrict H {a, dualPoly σ a} ⟨a, ha⟩)
    ⟨supportedRestrict_injective_of_paired H ha, supportedRestrict_surjective_of_paired H ha hne⟩

theorem blockApply_pairedFactorEquiv {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    (hne : a ≠ dualPoly σ a) (g : supportedUnitary B x {a, dualPoly σ a}) (v : V)
    (hv : v ∈ primaryComponent (x : Module.End K V) a) :
    blockApply (pairedFactorEquiv H ha hne g) v hv =
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v := rfl


omit H in
@[expose] def trivialOn (x : LinearMap.GeneralLinearGroup K V) (O : Set K[X]) :
    Subgroup (LinearMap.GeneralLinearGroup K V) where
  carrier := {g | ∀ b ∈ primaryFactors (x : Module.End K V), b ∈ O →
    ∀ v ∈ primaryComponent (x : Module.End K V) b, (g : Module.End K V) v = v}
  mul_mem' {g g'} hg hg' b hb hbO v hv := by
    rw [Units.val_mul, Module.End.mul_apply, hg' b hb hbO v hv, hg b hb hbO v hv]
  one_mem' _ _ _ _ _ := rfl
  inv_mem' {g} hg b hb hbO v hv := by
    have h1 := hg b hb hbO v hv
    calc ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v
        = ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
          ((g : Module.End K V) v) := by rw [h1]
      _ = v := by rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]; rfl

omit H in
theorem eq_one_of_forall_apply_eq (hsq : Squarefree (minpoly K (x : Module.End K V)))
    {g : LinearMap.GeneralLinearGroup K V}
    (h : ∀ b ∈ primaryFactors (x : Module.End K V),
      ∀ v ∈ primaryComponent (x : Module.End K V) b, (g : Module.End K V) v = v) : g = 1 :=
  Units.ext (ext_primaryComponent hsq fun b hb v hv => h b hb v hv)

theorem commute_of_disjoint {O O' : Set K[X]} (hd : Disjoint O O')
    {g g' : LinearMap.GeneralLinearGroup K V} (hg : g ∈ supportedUnitary B x O)
    (hg' : g' ∈ supportedUnitary B x O') : Commute g g' := by
  refine Units.ext (ext_primaryComponent H.squarefree fun b hb v hv => ?_)
  have hcomm := (mem_unitaryCentralizer.mp hg.1).2
  have hcomm' := (mem_unitaryCentralizer.mp hg'.1).2
  change (g : Module.End K V) ((g' : Module.End K V) v) =
    (g' : Module.End K V) ((g : Module.End K V) v)
  by_cases hO : b ∈ O
  · have hO' : b ∉ O' := fun h => Set.disjoint_left.mp hd hO h
    rw [hg'.2 b hb hO' v hv, hg'.2 b hb hO' _ (apply_mem_primaryComponent hcomm hv)]
  · by_cases hO' : b ∈ O'
    · rw [hg.2 b hb hO v hv, hg.2 b hb hO _ (apply_mem_primaryComponent hcomm' hv)]
    · rw [hg.2 b hb hO v hv, hg'.2 b hb hO' v hv, hg.2 b hb hO v hv]

theorem iSupIndep_supportedUnitary {orbits : Set (Set K[X])}
    (hdisj : ∀ O ∈ orbits, ∀ O' ∈ orbits, O ≠ O' → Disjoint O O') :
    iSupIndep (fun O : orbits => supportedUnitary B x (O : Set K[X])) := by
  intro O
  rw [Subgroup.disjoint_def]
  intro g hgO hgsup
  have hle : (⨆ (O' : orbits) (_ : O' ≠ O), supportedUnitary B x (O' : Set K[X])) ≤
      trivialOn x (O : Set K[X]) := by
    refine iSup₂_le fun O' hO' g' hg' b hb hbO v hv => ?_
    have hd := hdisj O' O'.2 O O.2 (fun h => hO' (Subtype.ext h))
    exact hg'.2 b hb (fun h => Set.disjoint_left.mp hd h hbO) v hv
  have hgT := hle hgsup
  refine eq_one_of_forall_apply_eq H.squarefree fun b hb v hv => ?_
  by_cases hbO : b ∈ (O : Set K[X])
  · exact hgT b hb hbO v hv
  · exact hgO.2 b hb hbO v hv


theorem exists_component {O : Set K[X]}
    (hO : ∀ b ∈ primaryFactors (x : Module.End K V), b ∈ O → dualPoly σ b ∈ O)
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ unitaryCentralizer B x) :
    ∃ gO ∈ supportedUnitary B x O, ∀ b ∈ primaryFactors (x : Module.End K V), b ∈ O →
      ∀ v ∈ primaryComponent (x : Module.End K V) b,
        (gO : Module.End K V) v = (g : Module.End K V) v := by
  classical
  have hsq := H.squarefree
  let g' : gl_centralizer x := ⟨g, (mem_unitaryCentralizer.mp hg).2 |> mem_gl_centralizer.mpr⟩
  let Γ : (b : primaryFactors (x : Module.End K V)) → blockGL (x : Module.End K V) (b : K[X]) :=
    fun b => if (b : K[X]) ∈ O then glCentralizerEquivPi hsq g' b else 1
  let gO : gl_centralizer x := (glCentralizerEquivPi hsq).symm Γ
  have hin : ∀ b ∈ primaryFactors (x : Module.End K V), b ∈ O →
      ∀ v ∈ primaryComponent (x : Module.End K V) b,
      ((gO : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
        (g : Module.End K V) v := by
    intro b hb hbO v hv
    rw [glue_apply H Γ ⟨b, hb⟩ hv]
    simp only [Γ, hbO, ↓reduceIte]
    rfl
  have hout : ∀ b ∈ primaryFactors (x : Module.End K V), b ∉ O →
      ∀ v ∈ primaryComponent (x : Module.End K V) b,
      ((gO : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
    intro b hb hbO v hv
    rw [glue_apply H Γ ⟨b, hb⟩ hv]
    simp only [Γ, hbO, ↓reduceIte]
    rfl
  refine ⟨(gO : LinearMap.GeneralLinearGroup K V), ⟨?_, hout⟩, hin⟩
  refine (mem_unitaryCentralizer_iff_blocks H).mpr ⟨mem_gl_centralizer.mp gO.2, ?_⟩
  intro c hc v hv w hw
  by_cases hcO : c ∈ O
  · rw [hin c hc hcO v hv, hin (dualPoly σ c) (dualPoly_mem_primaryFactors H hc) (hO c hc hcO) w hw]
    exact ((mem_unitaryCentralizer_iff_blocks H).mp hg).2 c hc v hv w hw
  · have hcO' : dualPoly σ c ∉ O := fun h => hcO (by
      have := hO _ (dualPoly_mem_primaryFactors H hc) h
      rwa [dualPoly_dualPoly_of_mem H hc] at this)
    rw [hout c hc hcO v hv, hout (dualPoly σ c) (dualPoly_mem_primaryFactors H hc) hcO' w hw]

theorem unitaryCentralizer_le_iSup {orbits : Set (Set K[X])}
    (hcov : ∀ b ∈ primaryFactors (x : Module.End K V), ∃ O ∈ orbits, b ∈ O)
    (hcl : ∀ O ∈ orbits, ∀ b ∈ primaryFactors (x : Module.End K V), b ∈ O → dualPoly σ b ∈ O) :
    unitaryCentralizer B x ≤ ⨆ O : orbits, supportedUnitary B x (O : Set K[X]) := by
  classical
  have hsq := H.squarefree
  set M := ⨆ O : orbits, supportedUnitary B x (O : Set K[X]) with hM
  suffices key : ∀ F : Finset K[X], ∀ g ∈ unitaryCentralizer B x,
      (∀ b ∈ primaryFactors (x : Module.End K V), b ∉ F →
        ∀ v ∈ primaryComponent (x : Module.End K V) b, (g : Module.End K V) v = v) → g ∈ M by
    intro g hg
    exact key (primaryFactors (x : Module.End K V)) g hg fun b hb hbn => absurd hb hbn
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro g hg h
    have : g = 1 := eq_one_of_forall_apply_eq hsq fun b hb v hv => h b hb (by simp) v hv
    rw [this]; exact M.one_mem
  | insert b F hbF ih =>
    intro g hg h
    by_cases hbΦ : b ∈ primaryFactors (x : Module.End K V)
    · obtain ⟨O, hO, hbO⟩ := hcov b hbΦ
      obtain ⟨gO, hgO, hgOeq⟩ := exists_component H (hcl O hO) hg
      have hgOM : gO ∈ M := (le_iSup (fun O : orbits => supportedUnitary B x (O : Set K[X]))
        ⟨O, hO⟩) hgO
      have hg' : gO⁻¹ * g ∈ unitaryCentralizer B x :=
        (unitaryCentralizer B x).mul_mem ((unitaryCentralizer B x).inv_mem hgO.1) hg
      have h' : ∀ c ∈ primaryFactors (x : Module.End K V), c ∉ F →
          ∀ v ∈ primaryComponent (x : Module.End K V) c,
          ((gO⁻¹ * g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
        intro c hc hcF v hv
        have hgv : (g : Module.End K V) v ∈ primaryComponent (x : Module.End K V) c :=
          apply_mem_primaryComponent (mem_unitaryCentralizer.mp hg).2 hv
        have hinv : ∀ u, ((gO⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
            ((gO : Module.End K V) u) = u := fun u => by
          rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]; rfl
        by_cases hcO : c ∈ O
        · rw [Units.val_mul, Module.End.mul_apply, ← hgOeq c hc hcO v hv, hinv]
        · have hgo : (gO : Module.End K V) v = v := hgO.2 c hc hcO v hv
          have hcb : c ∉ insert b F := by
            simp only [Finset.mem_insert, not_or]
            exact ⟨fun h => hcO (h ▸ hbO), hcF⟩
          rw [Units.val_mul, Module.End.mul_apply, h c hc hcb v hv]
          rw [← hgo, hinv, hgo]
      have := ih _ hg' h'
      have hg_eq : g = gO * (gO⁻¹ * g) := by simp
      rw [hg_eq]
      exact M.mul_mem hgOM this
    · refine ih g hg fun c hc hcF v hv => h c hc ?_ v hv
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hbΦ (h ▸ hc), hcF⟩

end Unitary

end Centralizer

end CFSG.RankThree.PartOne.KCUnitary

module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModC
import all CFSG.Fischer.F4
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.Bool
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Fischer

abbrev GL3 : Type := Matrix.GeneralLinearGroup (Fin 3) F4

@[expose] def scalars : Subgroup GL3 where
  carrier := {g | ∃ c : F4, (g : Matrix (Fin 3) (Fin 3) F4) = c • 1}
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_mul, hc, hd, smul_mul_smul_comm, one_mul, mul_comm]
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro g ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      have h := g.isUnit
      rw [hc, zero_smul] at h
      exact not_isUnit_zero h
    refine ⟨c⁻¹, ?_⟩
    rw [Matrix.coe_units_inv, hc]
    exact Matrix.inv_eq_right_inv (by
      rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hc0, one_smul])

theorem mem_scalars {g : GL3} : g ∈ scalars ↔ ∃ c : F4, (g : Matrix (Fin 3) (Fin 3) F4) = c • 1 :=
  Iff.rfl

theorem scalar_ne_zero {g : GL3} {c : F4} (hc : (g : Matrix (Fin 3) (Fin 3) F4) = c • 1) :
    c ≠ 0 := by
  rintro rfl
  have h := g.isUnit
  rw [hc, zero_smul] at h
  exact not_isUnit_zero h

theorem card_units_F4 : (Finset.univ.filter fun c : F4 => c ≠ 0).card = 3 := by decide

@[expose] noncomputable def scalGL (c : F4) (hc : c ≠ 0) : GL3 :=
  ⟨c • 1, c⁻¹ • 1, by rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hc, one_smul], by
    rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hc, one_smul]⟩

theorem scalGL_mem (c : F4) (hc : c ≠ 0) : scalGL c hc ∈ scalars := ⟨c, rfl⟩

theorem card_scalars : Nat.card scalars = 3 := by
  classical
  have hent : ∀ g ∈ scalars, (g : Matrix (Fin 3) (Fin 3) F4) =
      ((g : Matrix (Fin 3) (Fin 3) F4) 0 0) • 1 := by
    rintro g ⟨c, hc⟩
    rw [hc]
    simp
  have e : {c : F4 // c ≠ 0} ≃ scalars :=
    { toFun := fun c => ⟨scalGL c.1 c.2, scalGL_mem c.1 c.2⟩
      invFun := fun g => ⟨((g : GL3) : Matrix (Fin 3) (Fin 3) F4) 0 0, by
        have h := hent g.1 g.2
        exact scalar_ne_zero h⟩
      left_inv := fun c => by
        apply Subtype.ext
        show ((c.1 • (1 : Matrix (Fin 3) (Fin 3) F4)) 0 0) = c.1
        simp
      right_inv := fun g => by
        apply Subtype.ext
        apply Units.ext
        exact (hent g.1 g.2).symm }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_units_F4

variable (Γ : Subgroup GL3) (x₀ : Fin 3 → F4)

@[expose] def orb : Set (Fin 3 → F4) :=
  {y | ∃ γ ∈ Γ, (γ : Matrix (Fin 3) (Fin 3) F4).mulVec x₀ = y}

variable {Γ x₀}

theorem mem_orb_self : x₀ ∈ orb Γ x₀ := ⟨1, Γ.one_mem, by simp⟩

theorem orb_smul {γ : GL3} (hγ : γ ∈ Γ) {y : Fin 3 → F4} (hy : y ∈ orb Γ x₀) :
    (γ : Matrix (Fin 3) (Fin 3) F4).mulVec y ∈ orb Γ x₀ := by
  obtain ⟨δ, hδ, rfl⟩ := hy
  exact ⟨γ * δ, Γ.mul_mem hγ hδ, by rw [Matrix.GeneralLinearGroup.coe_mul,
    Matrix.mulVec_mulVec]⟩

theorem orb_scal (hsc : scalars ≤ Γ) {c : F4} (hc : c ≠ 0) {y : Fin 3 → F4}
    (hy : y ∈ orb Γ x₀) : c • y ∈ orb Γ x₀ := by
  have h := orb_smul (hsc (scalGL_mem c hc)) hy
  have e : ((scalGL c hc : GL3) : Matrix (Fin 3) (Fin 3) F4).mulVec y = c • y := by
    show (c • (1 : Matrix (Fin 3) (Fin 3) F4)).mulVec y = c • y
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rwa [e] at h

theorem orb_ne_zero (h0 : x₀ ≠ 0) {y : Fin 3 → F4} (hy : y ∈ orb Γ x₀) : y ≠ 0 := by
  obtain ⟨γ, -, rfl⟩ := hy
  intro h
  apply h0
  have e := congrArg (fun z => ((γ⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) F4).mulVec z) h
  simpa [Matrix.mulVec_mulVec] using e

theorem orb_finite : (orb Γ x₀).Finite := Set.toFinite _

@[expose] noncomputable def pts (Γ : Subgroup GL3) (x₀ : Fin 3 → F4) : Finset ℕ :=
  (orb_finite (Γ := Γ) (x₀ := x₀)).toFinset.image ptc

theorem mem_pts {p : ℕ} : p ∈ pts Γ x₀ ↔ ∃ y ∈ orb Γ x₀, ptc y = p := by
  simp [pts]

theorem card_fiber (hsc : scalars ≤ Γ) (h0 : x₀ ≠ 0) {y : Fin 3 → F4} (hy : y ∈ orb Γ x₀) :
    ((orb_finite (Γ := Γ) (x₀ := x₀)).toFinset.filter fun z => ptc z = ptc y).card = 3 := by
  classical
  have hy0 := orb_ne_zero h0 hy
  have e : ((orb_finite (Γ := Γ) (x₀ := x₀)).toFinset.filter fun z => ptc z = ptc y) =
      (Finset.univ.filter fun c : F4 => c ≠ 0).image fun c => c • y := by
    ext z
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨hz, hpz⟩
      obtain ⟨c, hc, rfl⟩ := eq_smul_of_ptc_eq hy0 (orb_ne_zero h0 hz) hpz.symm
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨orb_scal hsc hc hy, ptc_smul hc y⟩
  rw [e, Finset.card_image_of_injective _ (smul_left_injective F4 hy0), card_units_F4]

theorem card_pts (hsc : scalars ≤ Γ) (h0 : x₀ ≠ 0) (h18 : Nat.card (orb Γ x₀) = 18) :
    (pts Γ x₀).card = 6 := by
  classical
  have hS : (orb_finite (Γ := Γ) (x₀ := x₀)).toFinset.card = 18 := by
    rw [← h18, Nat.card_eq_card_finite_toFinset]
  have hsum := Finset.card_eq_sum_card_image ptc (orb_finite (Γ := Γ) (x₀ := x₀)).toFinset
  have hc : ∀ p ∈ (orb_finite (Γ := Γ) (x₀ := x₀)).toFinset.image ptc,
      ((orb_finite (Γ := Γ) (x₀ := x₀)).toFinset.filter fun z => ptc z = p).card = 3 := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
    exact card_fiber hsc h0 ((orb_finite (Γ := Γ) (x₀ := x₀)).mem_toFinset.mp hy)
  rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, hS] at hsum
  show ((orb_finite (Γ := Γ) (x₀ := x₀)).toFinset.image ptc).card = 6
  omega

theorem pts_spec (h0 : x₀ ≠ 0) {p : ℕ} (hp : p ∈ pts Γ x₀) :
    ∃ y ∈ orb Γ x₀, ∃ c : F4, c ≠ 0 ∧ decV p = c • y := by
  obtain ⟨y, hy, rfl⟩ := mem_pts.mp hp
  obtain ⟨c, hc, he⟩ := decV_ptc (orb_ne_zero h0 hy)
  exact ⟨y, hy, c, hc, he⟩

theorem pts_lt {p : ℕ} (hp : p ∈ pts Γ x₀) : p < 64 := by
  obtain ⟨y, -, rfl⟩ := mem_pts.mp hp
  exact ptc_lt y

theorem pts_pn {p : ℕ} (hp : p ∈ pts Γ x₀) : pn p = p := by
  obtain ⟨y, -, rfl⟩ := mem_pts.mp hp
  exact pn_pn _ (encV_lt y)

theorem pts_ne_zero (h0 : x₀ ≠ 0) {p : ℕ} (hp : p ∈ pts Γ x₀) : p ≠ 0 := by
  obtain ⟨y, hy, rfl⟩ := mem_pts.mp hp
  exact pn_ne_zero _ (encV_lt y) (encV_ne_zero (orb_ne_zero h0 hy))

theorem pts_mem_ptCodes (h0 : x₀ ≠ 0) {p : ℕ} (hp : p ∈ pts Γ x₀) : p ∈ ptCodes :=
  (mem_ptCodes_iff p (pts_lt hp)).2 ⟨pts_ne_zero h0 hp, pts_pn hp⟩

theorem decV_ne_zero_of_pts (h0 : x₀ ≠ 0) {p : ℕ} (hp : p ∈ pts Γ x₀) : decV p ≠ 0 :=
  decV_ne_zero (pts_lt hp) (pts_ne_zero h0 hp)

@[expose] def actP (γ : GL3) (p : ℕ) : ℕ := ptc ((γ : Matrix (Fin 3) (Fin 3) F4).mulVec (decV p))

theorem mulVec_ne_zero (γ : GL3) {x : Fin 3 → F4} (hx : x ≠ 0) :
    (γ : Matrix (Fin 3) (Fin 3) F4).mulVec x ≠ 0 := by
  intro h
  apply hx
  have e := congrArg (fun z => ((γ⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) F4).mulVec z) h
  simpa [Matrix.mulVec_mulVec] using e

theorem actP_mem (h0 : x₀ ≠ 0) {γ : GL3} (hγ : γ ∈ Γ) {p : ℕ} (hp : p ∈ pts Γ x₀) :
    actP γ p ∈ pts Γ x₀ := by
  obtain ⟨y, hy, c, hc, he⟩ := pts_spec h0 hp
  rw [actP, he, Matrix.mulVec_smul, ptc_smul hc]
  exact mem_pts.2 ⟨_, orb_smul hγ hy, rfl⟩

theorem decV_actP (γ : GL3) {p : ℕ} (hp : decV p ≠ 0) :
    ∃ c : F4, c ≠ 0 ∧ decV (actP γ p) = c • (γ : Matrix (Fin 3) (Fin 3) F4).mulVec (decV p) :=
  decV_ptc (mulVec_ne_zero γ hp)

theorem actP_lt (γ : GL3) (p : ℕ) : actP γ p < 64 := ptc_lt _

theorem decV_actP_ne_zero (γ : GL3) {p : ℕ} (hp : decV p ≠ 0) : decV (actP γ p) ≠ 0 :=
  decV_ptc_ne_zero (mulVec_ne_zero γ hp)

theorem actP_mul (γ δ : GL3) {p : ℕ} (hp : decV p ≠ 0) :
    actP (γ * δ) p = actP γ (actP δ p) := by
  obtain ⟨c, hc, he⟩ := decV_actP δ hp
  rw [actP, actP, he, Matrix.mulVec_smul, ptc_smul hc, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.mulVec_mulVec]

theorem actP_one {p : ℕ} (hp : p < 64) (hpn : pn p = p) : actP 1 p = p := by
  rw [actP, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  exact ptc_decV hp hpn

theorem actP_inv_actP (γ : GL3) {p : ℕ} (hp : p < 64) (hpn : pn p = p) (h0 : p ≠ 0) :
    actP γ⁻¹ (actP γ p) = p := by
  rw [← actP_mul _ _ (decV_ne_zero hp h0), inv_mul_cancel, actP_one hp hpn]

theorem ptc_mulVec (γ : GL3) {x : Fin 3 → F4} (hx : x ≠ 0) :
    ptc ((γ : Matrix (Fin 3) (Fin 3) F4).mulVec x) = actP γ (ptc x) := by
  obtain ⟨c, hc, he⟩ := decV_ptc hx
  rw [actP, he, Matrix.mulVec_smul, ptc_smul hc]

theorem actP_one_pts {p : ℕ} (hp : p ∈ pts Γ x₀) : actP 1 p = p :=
  actP_one (pts_lt hp) (pts_pn hp)

@[expose] noncomputable def permOf (Γ : Subgroup GL3) (h0 : x₀ ≠ 0) (γ : ↥Γ) :
    Equiv.Perm ↥(pts Γ x₀) where
  toFun p := ⟨actP γ p, actP_mem h0 γ.2 p.2⟩
  invFun p := ⟨actP (γ⁻¹ : GL3) p, actP_mem h0 (Γ.inv_mem γ.2) p.2⟩
  left_inv p := by
    apply Subtype.ext
    show actP (γ⁻¹ : GL3) (actP γ p) = p
    rw [← actP_mul _ _ (decV_ne_zero_of_pts h0 p.2), inv_mul_cancel, actP_one_pts p.2]
  right_inv p := by
    apply Subtype.ext
    show actP (γ : GL3) (actP (γ⁻¹ : GL3) p) = p
    rw [← actP_mul _ _ (decV_ne_zero_of_pts h0 p.2), mul_inv_cancel, actP_one_pts p.2]

theorem permOf_apply (h0 : x₀ ≠ 0) (γ : ↥Γ) (p : ↥(pts Γ x₀)) :
    ((permOf Γ h0 γ p : ↥(pts Γ x₀)) : ℕ) = actP γ p := rfl

@[expose] noncomputable def piP (Γ : Subgroup GL3) (h0 : x₀ ≠ 0) :
    ↥Γ →* Equiv.Perm ↥(pts Γ x₀) where
  toFun := permOf Γ h0
  map_one' := by
    ext p
    exact actP_one_pts p.2
  map_mul' γ δ := by
    ext p
    exact actP_mul γ δ (decV_ne_zero_of_pts h0 p.2)

theorem piP_apply (h0 : x₀ ≠ 0) (γ : ↥Γ) (p : ↥(pts Γ x₀)) :
    ((piP Γ h0 γ p : ↥(pts Γ x₀)) : ℕ) = actP γ p := rfl

theorem actP_scalar {γ : GL3} (hγ : γ ∈ scalars) {p : ℕ} (hp : p ∈ pts Γ x₀) :
    actP γ p = p := by
  obtain ⟨c, hc⟩ := hγ
  rw [actP, hc, Matrix.smul_mulVec, Matrix.one_mulVec, ptc_smul (scalar_ne_zero hc)]
  exact ptc_decV (pts_lt hp) (pts_pn hp)

theorem ker_piP (hsc : scalars ≤ Γ)
    (hsimple : ∀ N : Subgroup GL3, N ≤ Γ → (∀ g ∈ Γ, ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
      scalars ≤ N → N = scalars ∨ N = Γ)
    (h0 : x₀ ≠ 0) (h18 : Nat.card (orb Γ x₀) = 18) :
    (piP Γ h0).ker.map Γ.subtype = scalars := by
  classical
  set K := (piP Γ h0).ker.map Γ.subtype with hK
  have hKΓ : K ≤ Γ := Subgroup.map_subtype_le _
  have hmemK : ∀ γ : GL3, γ ∈ K ↔ γ ∈ Γ ∧ ∀ p ∈ pts Γ x₀, actP γ p = p := by
    intro γ
    constructor
    · rintro ⟨⟨γ, hγ⟩, hk, rfl⟩
      refine ⟨hγ, fun p hp => ?_⟩
      have := congrArg (fun σ : Equiv.Perm ↥(pts Γ x₀) => ((σ ⟨p, hp⟩ : ↥(pts Γ x₀)) : ℕ))
        (MonoidHom.mem_ker.mp hk)
      simpa [piP_apply] using this
    · rintro ⟨hγ, hfix⟩
      refine ⟨⟨γ, hγ⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      ext p
      exact hfix p p.2
  have hnorm : ∀ g ∈ Γ, ∀ n ∈ K, g * n * g⁻¹ ∈ K := by
    intro g hg n hn
    rw [hmemK] at hn ⊢
    refine ⟨Γ.mul_mem (Γ.mul_mem hg hn.1) (Γ.inv_mem hg), fun p hp => ?_⟩
    have hp' := actP_mem h0 (Γ.inv_mem hg) hp
    have hd := decV_ne_zero_of_pts h0 hp
    rw [actP_mul _ _ hd, actP_mul _ _ (decV_ne_zero_of_pts h0 hp'), hn.2 _ hp',
      ← actP_mul _ _ hd, mul_inv_cancel, actP_one_pts hp]
  have hscK : scalars ≤ K := fun γ hγ =>
    (hmemK γ).2 ⟨hsc hγ, fun p hp => actP_scalar hγ hp⟩
  rcases hsimple K hKΓ hnorm hscK with h | h
  · exact h
  · exfalso
    have hx₀p : ptc x₀ ∈ pts Γ x₀ := mem_pts.2 ⟨x₀, mem_orb_self, rfl⟩
    obtain ⟨c₀, hc₀, he₀⟩ := decV_ptc h0
    have hsub : orb Γ x₀ ⊆ (Finset.univ.filter fun c : F4 => c ≠ 0).image fun c => c • x₀ := by
      rintro y ⟨γ, hγ, rfl⟩
      have hfix := ((hmemK γ).1 (h ▸ hγ)).2 _ hx₀p
      rw [actP, he₀, Matrix.mulVec_smul, ptc_smul hc₀] at hfix
      obtain ⟨d, hd, hde⟩ := eq_smul_of_ptc_eq h0 (mulVec_ne_zero γ h0) hfix.symm
      simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image,
        Set.mem_ofPred_eq]
      exact ⟨d, hd, hde.symm⟩
    have hle := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ (smul_left_injective F4 h0),
      card_units_F4, ← Nat.card_coe_set_eq, h18] at hle
    omega

section Main

@[expose] def SimpleMod (Γ : Subgroup GL3) : Prop :=
  ∀ N : Subgroup GL3, N ≤ Γ → (∀ g ∈ Γ, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → scalars ≤ N →
    N = scalars ∨ N = Γ

theorem card_P (hsc : scalars ≤ Γ) (h0 : x₀ ≠ 0) (h18 : Nat.card (orb Γ x₀) = 18) :
    Nat.card ↥(pts Γ x₀) = 6 := by
  rw [Nat.card_eq_finsetCard]
  exact card_pts hsc h0 h18

theorem card_range_piP (hcard : Nat.card Γ = 1080) (hsc : scalars ≤ Γ) (hsimple : SimpleMod Γ)
    (h0 : x₀ ≠ 0) (h18 : Nat.card (orb Γ x₀) = 18) : Nat.card (piP Γ h0).range = 360 := by
  have h1 := Subgroup.card_ker_mul_card_range (piP Γ h0)
  have hker : Nat.card (piP Γ h0).ker = 3 := by
    have h := card_scalars
    rw [← ker_piP hsc hsimple h0 h18, Subgroup.card_map_of_injective Γ.subtype_injective] at h
    exact h
  rw [hker, hcard] at h1
  omega

theorem range_piP (hcard : Nat.card Γ = 1080) (hsc : scalars ≤ Γ) (hsimple : SimpleMod Γ)
    (h0 : x₀ ≠ 0) (h18 : Nat.card (orb Γ x₀) = 18) :
    (piP Γ h0).range = alternatingGroup ↥(pts Γ x₀) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  have h := Subgroup.card_mul_index (piP Γ h0).range
  rw [Nat.card_perm, card_P hsc h0 h18, card_range_piP hcard hsc hsimple h0 h18] at h
  have h720 : Nat.factorial 6 = 720 := by decide
  rw [h720] at h
  omega

theorem exists_trans3 (hcard : Nat.card Γ = 1080) (hsc : scalars ≤ Γ) (hsimple : SimpleMod Γ)
    (h0 : x₀ ≠ 0) (h18 : Nat.card (orb Γ x₀) = 18) {p q r p' q' r' : ↥(pts Γ x₀)}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hpq' : p' ≠ q') (hpr' : p' ≠ r') (hqr' : q' ≠ r') :
    ∃ γ ∈ Γ, actP γ p = p' ∧ actP γ q = q' ∧ actP γ r = r' := by
  classical
  have hP := card_P hsc h0 h18
  have h4 := alternatingGroup.isMultiplyPretransitive ↥(pts Γ x₀)
  have h3 : MulAction.IsMultiplyPretransitive (alternatingGroup ↥(pts Γ x₀)) ↥(pts Γ x₀) 3 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card ↥(pts Γ x₀) - 2) (by omega)
      (by omega)
  have hinj : ∀ {a b c : ↥(pts Γ x₀)}, a ≠ b → a ≠ c → b ≠ c → Function.Injective ![a, b, c] := by
    intro a b c hab hac hbc i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  let u : Fin 3 ↪ ↥(pts Γ x₀) := ⟨![p, q, r], hinj hpq hpr hqr⟩
  let v : Fin 3 ↪ ↥(pts Γ x₀) := ⟨![p', q', r'], hinj hpq' hpr' hqr'⟩
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup ↥(pts Γ x₀)) u v
  have hσr : (σ : Equiv.Perm ↥(pts Γ x₀)) ∈ (piP Γ h0).range := by
    rw [range_piP hcard hsc hsimple h0 h18]
    exact σ.2
  obtain ⟨γ, hγ⟩ := hσr
  have key : ∀ i : Fin 3, actP γ (u i) = v i := by
    intro i
    have h1 := congrArg (fun f : Fin 3 ↪ ↥(pts Γ x₀) => ((f i : ↥(pts Γ x₀)) : ℕ)) hσ
    simp only [Function.Embedding.smul_apply] at h1
    rw [← h1, ← piP_apply h0, hγ]
    rfl
  exact ⟨γ, γ.2, key 0, key 1, key 2⟩

theorem ind3_pts (hcard : Nat.card Γ = 1080) (hsc : scalars ≤ Γ) (hsimple : SimpleMod Γ)
    (h0 : x₀ ≠ 0) (h18 : Nat.card (orb Γ x₀) = 18) {p q r : ℕ} (hp : p ∈ pts Γ x₀)
    (hq : q ∈ pts Γ x₀) (hr : r ∈ pts Γ x₀) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Ind3 (decV p) (decV q) (decV r) := by
  classical
  by_contra hdep
  have hall : ∀ a ∈ pts Γ x₀, ∀ b ∈ pts Γ x₀, ∀ c ∈ pts Γ x₀, a ≠ b → a ≠ c → b ≠ c →
      ¬ Ind3 (decV a) (decV b) (decV c) := by
    intro a ha b hb c hc hab hac hbc hind
    have hne : ∀ {u v : ℕ} {hu : u ∈ pts Γ x₀} {hv : v ∈ pts Γ x₀}, u ≠ v →
        (⟨u, hu⟩ : ↥(pts Γ x₀)) ≠ ⟨v, hv⟩ := fun h e => h (congrArg Subtype.val e)
    obtain ⟨γ, hγ, e1, e2, e3⟩ := exists_trans3 hcard hsc hsimple h0 h18
      (hne (hu := hp) (hv := hq) hpq) (hne (hu := hp) (hv := hr) hpr)
      (hne (hu := hq) (hv := hr) hqr) (hne (hu := ha) (hv := hb) hab)
      (hne (hu := ha) (hv := hc) hac) (hne (hu := hb) (hv := hc) hbc)
    obtain ⟨c1, hc1, f1⟩ := decV_actP γ (decV_ne_zero_of_pts h0 hp)
    obtain ⟨c2, hc2, f2⟩ := decV_actP γ (decV_ne_zero_of_pts h0 hq)
    obtain ⟨c3, hc3, f3⟩ := decV_actP γ (decV_ne_zero_of_pts h0 hr)
    simp only at e1 e2 e3
    rw [e1] at f1
    rw [e2] at f2
    rw [e3] at f3
    rw [f1, f2, f3] at hind
    have h1 := (hind.smul (inv_ne_zero hc1) (inv_ne_zero hc2) (inv_ne_zero hc3)).map γ⁻¹
    simp only [smul_smul, inv_mul_cancel₀ hc1, inv_mul_cancel₀ hc2, inv_mul_cancel₀ hc3,
      one_smul, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] at h1
    exact hdep h1
  have hP := card_pts hsc h0 h18
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ pts Γ x₀, ∃ b ∈ pts Γ x₀, a ≠ b := by
    exact ⟨p, hp, q, hq, hpq⟩
  have hsub : pts Γ x₀ ⊆ (onLine a b).toFinset := by
    intro c hc
    rw [List.mem_toFinset, onLine, List.mem_filter]
    refine ⟨pts_mem_ptCodes h0 hc, ?_⟩
    rw [Bool.not_eq_eq_eq_not, Bool.not_true]
    by_cases hca : c = a
    · subst hca
      by_contra h
      rw [Bool.not_eq_false] at h
      have := (indep3_iff (pts_lt ha) (pts_lt hb) (pts_lt ha)).1 h
      obtain ⟨h1, -, -⟩ := this 1 0 1 (by
        rw [one_smul, zero_smul, add_zero, ← two_smul F4, F4.two_eq_zero, zero_smul])
      exact one_ne_zero h1
    by_cases hcb : c = b
    · subst hcb
      by_contra h
      rw [Bool.not_eq_false] at h
      have := (indep3_iff (pts_lt ha) (pts_lt hc) (pts_lt hc)).1 h
      obtain ⟨-, h1, -⟩ := this 0 1 1 (by
        rw [one_smul, zero_smul, zero_add, ← two_smul F4, F4.two_eq_zero, zero_smul])
      exact one_ne_zero h1
    by_contra h
    rw [Bool.not_eq_false] at h
    exact hall a ha b hb c hc hab (Ne.symm hca) (Ne.symm hcb)
      ((indep3_iff (pts_lt ha) (pts_lt hb) (pts_lt hc)).1 h)
  have hle := Finset.card_le_card hsub
  have h5 := onLine_length a (pts_mem_ptCodes h0 ha) b (pts_mem_ptCodes h0 hb) hab
  have := List.toFinset_card_le (onLine a b)
  omega

theorem arc_map (hcard : Nat.card Γ = 1080) (hsc : scalars ≤ Γ) (hsimple : SimpleMod Γ)
    (h0 : x₀ ≠ 0) (h18 : Nat.card (orb Γ x₀) = 18) (g : GL3) {l : List ℕ}
    (hl : ∀ u ∈ l, u ∈ pts Γ x₀) : arc (l.map (actP g)) = true := by
  simp only [arc, List.all_map, List.all_eq_true, Function.comp_apply, Bool.or_eq_true,
    beq_iff_eq]
  intro u hu v hv w hw
  by_cases huv : u = v
  · exact Or.inl (Or.inl (Or.inl (by rw [huv])))
  by_cases huw : u = w
  · exact Or.inl (Or.inl (Or.inr (by rw [huw])))
  by_cases hvw : v = w
  · exact Or.inl (Or.inr (by rw [hvw]))
  right
  rw [indep3_iff (actP_lt g u) (actP_lt g v) (actP_lt g w)]
  obtain ⟨c1, hc1, e1⟩ := decV_actP g (decV_ne_zero_of_pts h0 (hl u hu))
  obtain ⟨c2, hc2, e2⟩ := decV_actP g (decV_ne_zero_of_pts h0 (hl v hv))
  obtain ⟨c3, hc3, e3⟩ := decV_actP g (decV_ne_zero_of_pts h0 (hl w hw))
  rw [e1, e2, e3]
  exact ((ind3_pts hcard hsc hsimple h0 h18 (hl u hu) (hl v hv) (hl w hw) huv huw hvw).map
    g).smul hc1 hc2 hc3

theorem ne_zero_of_card_orb (h18 : Nat.card (orb Γ x₀) = 18) : x₀ ≠ 0 := by
  rintro rfl
  have e : orb Γ 0 = {0} := by
    ext y
    simp only [orb, Set.mem_ofPred_eq, Matrix.mulVec_zero, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, -, rfl⟩
      rfl
    · rintro rfl
      exact ⟨1, Γ.one_mem, rfl⟩
  rw [e, Nat.card_unique] at h18
  omega

theorem ptc_mem_ptCodes {x : Fin 3 → F4} (hx : x ≠ 0) : ptc x ∈ ptCodes :=
  (mem_ptCodes_iff _ (ptc_lt x)).2 ⟨pn_ne_zero _ (encV_lt x) (encV_ne_zero hx),
    pn_pn _ (encV_lt x)⟩

theorem oVec_ne_zero {x : Fin 3 → F4} (hx : x ∈ oVec) : x ≠ 0 := by
  obtain ⟨p, hp, c, hc, rfl⟩ := hx
  exact smul_ne_zero hc (decV_ne_zero (oPts_lt p hp) (oPts_ne_zero p hp))

theorem exists_pts_oPts (hcard : Nat.card Γ = 1080) (hsc : scalars ≤ Γ)
    (hsimple : SimpleMod Γ) (h18 : Nat.card (orb Γ x₀) = 18) :
    ∃ g : GL3, (∀ p ∈ pts Γ x₀, actP g p ∈ oPts) ∧ ∀ o ∈ oPts, ∃ p ∈ pts Γ x₀, actP g p = o := by
  classical
  have h0 := ne_zero_of_card_orb h18
  obtain ⟨a1, t1, ha1, hP1, ht1⟩ := Finset.card_eq_succ.mp (card_pts hsc h0 h18)
  obtain ⟨a2, t2, ha2, rfl, ht2⟩ := Finset.card_eq_succ.mp ht1
  obtain ⟨a3, t3, ha3, rfl, ht3⟩ := Finset.card_eq_succ.mp ht2
  obtain ⟨a4, t4, ha4, rfl, ht4⟩ := Finset.card_eq_succ.mp ht3
  obtain ⟨q, r, hqr, rfl⟩ := Finset.card_eq_two.mp ht4
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha1 ha2 ha3 ha4
  obtain ⟨h12, h13, h14, h1q, h1r⟩ := ha1
  obtain ⟨h23, h24, h2q, h2r⟩ := ha2
  obtain ⟨h34, h3q, h3r⟩ := ha3
  obtain ⟨h4q, h4r⟩ := ha4
  have hmem : ∀ u, u ∈ pts Γ x₀ ↔ u = a1 ∨ u = a2 ∨ u = a3 ∨ u = a4 ∨ u = q ∨ u = r := by
    intro u
    rw [← hP1]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  have m1 : a1 ∈ pts Γ x₀ := (hmem a1).2 (by simp)
  have m2 : a2 ∈ pts Γ x₀ := (hmem a2).2 (by simp)
  have m3 : a3 ∈ pts Γ x₀ := (hmem a3).2 (by simp)
  have m4 : a4 ∈ pts Γ x₀ := (hmem a4).2 (by simp)
  have mq : q ∈ pts Γ x₀ := (hmem q).2 (by simp)
  have mr : r ∈ pts Γ x₀ := (hmem r).2 (by simp)
  have I := fun {u v w : ℕ} (hu : u ∈ pts Γ x₀) (hv : v ∈ pts Γ x₀) (hw : w ∈ pts Γ x₀)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) =>
    ind3_pts hcard hsc hsimple h0 h18 hu hv hw huv huw hvw
  obtain ⟨g, ⟨c1, hc1, e1⟩, ⟨c2, hc2, e2⟩, ⟨c3, hc3, e3⟩, e4⟩ :=
    exists_frame (I m1 m2 m3 h12 h13 h23) (I m1 m2 m4 h12 h14 h24) (I m1 m3 m4 h13 h14 h34)
      (I m2 m3 m4 h23 h24 h34)
  have f1 : actP g a1 = 1 := by
    rw [actP, e1, ptc_smul hc1]
    exact ptc_decV (by norm_num) (by decide)
  have f2 : actP g a2 = 4 := by
    rw [actP, e2, ptc_smul hc2]
    exact ptc_decV (by norm_num) (by decide)
  have f3 : actP g a3 = 16 := by
    rw [actP, e3, ptc_smul hc3]
    exact ptc_decV (by norm_num) (by decide)
  have f4 : actP g a4 = 21 := by
    rw [actP, e4]
    exact ptc_decV (by norm_num) (by decide)
  have harc := arc_map hcard hsc hsimple h0 h18 g (l := [a1, a2, a3, a4, q, r]) (by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    exact (hmem u).2 hu)
  simp only [List.map_cons, List.map_nil, f1, f2, f3, f4] at harc
  have hinj : ∀ {u v : ℕ}, u ∈ pts Γ x₀ → v ∈ pts Γ x₀ → actP g u = actP g v → u = v := by
    intro u v hu hv he
    rw [← actP_inv_actP g (pts_lt hu) (pts_pn hu) (pts_ne_zero h0 hu), he,
      actP_inv_actP g (pts_lt hv) (pts_pn hv) (pts_ne_zero h0 hv)]
  have hcode : ∀ {u : ℕ}, u ∈ pts Γ x₀ → actP g u ∈ ptCodes := fun hu =>
    ptc_mem_ptCodes (mulVec_ne_zero g (decV_ne_zero_of_pts h0 hu))
  have hfr : ∀ {u : ℕ}, u ∈ pts Γ x₀ → u ≠ a1 → u ≠ a2 → u ≠ a3 → u ≠ a4 →
      actP g u ∉ [1, 4, 16, 21] := by
    intro u hu n1 n2 n3 n4 h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h
    · exact n1 (hinj hu m1 (h.trans f1.symm))
    · exact n2 (hinj hu m2 (h.trans f2.symm))
    · exact n3 (hinj hu m3 (h.trans f3.symm))
    · exact n4 (hinj hu m4 (h.trans f4.symm))
  have hqr' : actP g q ≠ actP g r := fun h => hqr (hinj mq mr h)
  obtain h | h | h | h | h := arc_unique _ (hcode mq) _ (hcode mr) harc
  · refine ⟨g, fun p hp => ?_, fun o ho => ?_⟩
    · rcases (hmem p).1 hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [oPts, f1, f2, f3, f4, h.1, h.2]
    · simp only [oPts, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [⟨a1, m1, f1⟩, ⟨a2, m2, f2⟩, ⟨a3, m3, f3⟩, ⟨a4, m4, f4⟩, ⟨q, mq, h.1⟩,
        ⟨r, mr, h.2⟩]
  · refine ⟨g, fun p hp => ?_, fun o ho => ?_⟩
    · rcases (hmem p).1 hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [oPts, f1, f2, f3, f4, h.1, h.2]
    · simp only [oPts, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [⟨a1, m1, f1⟩, ⟨a2, m2, f2⟩, ⟨a3, m3, f3⟩, ⟨a4, m4, f4⟩, ⟨r, mr, h.2⟩,
        ⟨q, mq, h.1⟩]
  · exact absurd h hqr'
  · exact absurd h (hfr mq (Ne.symm h1q) (Ne.symm h2q) (Ne.symm h3q) (Ne.symm h4q))
  · exact absurd h (hfr mr (Ne.symm h1r) (Ne.symm h2r) (Ne.symm h3r) (Ne.symm h4r))

theorem exists_conj_gm (hcard : Nat.card Γ = 1080)
    (hsc : scalars ≤ Γ) (hsimple : SimpleMod Γ) (h18 : Nat.card (orb Γ x₀) = 18) :
    ∃ g : GL3, ∀ γ : GL3, γ ∈ Γ ↔ g * γ * g⁻¹ ∈ gm := by
  classical
  have h0 := ne_zero_of_card_orb h18
  obtain ⟨g, hinto, hsurj⟩ := exists_pts_oPts hcard hsc hsimple h18
  have hle : ∀ γ ∈ Γ, g * γ * g⁻¹ ∈ gm := by
    intro γ hγ x hx
    have hx0 := oVec_ne_zero hx
    rw [mem_oVec_iff] at hx ⊢
    change ptc x ∈ oPts at hx
    change ptc _ ∈ oPts
    obtain ⟨p, hp, hpo⟩ := hsurj _ hx
    have hd := decV_ne_zero_of_pts h0 hp
    rw [ptc_mulVec _ hx0, ← hpo, actP_mul _ _ (decV_actP_ne_zero g hd),
      actP_inv_actP g (pts_lt hp) (pts_pn hp) (pts_ne_zero h0 hp), actP_mul _ _ hd]
    exact hinto _ (actP_mem h0 hγ hp)
  refine ⟨g, fun γ => ⟨hle γ, fun h => ?_⟩⟩
  let f : ↥Γ → ↥gm := fun δ => ⟨g * δ * g⁻¹, hle δ δ.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    simpa [f] using this
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, card_gm])
  obtain ⟨δ, hδ⟩ := hbij.2 ⟨g * γ * g⁻¹, h⟩
  have e := congrArg Subtype.val hδ
  simp only [f, mul_left_inj, mul_right_inj] at e
  rw [← e]
  exact δ.2

end Main

end CFSG.Quasithin.H13.S127.Mod

end

module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.Singer

open scoped LinearAlgebra.Projectivization Pointwise
open Projectivization Module

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

@[expose] def pointsIn (W : Submodule k V) : Set (ℙ k V) := {p | p.submodule ≤ W}

theorem mem_pointsIn {W : Submodule k V} {p : ℙ k V} : p ∈ pointsIn W ↔ p.submodule ≤ W :=
  Iff.rfl

theorem mk_mem_pointsIn {W : Submodule k V} {v : V} (hv : v ≠ 0) :
    mk k v hv ∈ pointsIn W ↔ v ∈ W := by
  rw [mem_pointsIn, submodule_mk, Submodule.span_singleton_le_iff_mem]

theorem rep_mem_iff_mem_pointsIn {W : Submodule k V} {p : ℙ k V} :
    p.rep ∈ W ↔ p ∈ pointsIn W := by
  conv_rhs => rw [← mk_rep p]
  rw [mk_mem_pointsIn]

theorem pointsIn_mono {W W' : Submodule k V} (h : W ≤ W') : pointsIn W ⊆ pointsIn W' :=
  fun _ hp => le_trans hp h

theorem eq_of_mem_pointsIn_submodule {p q : ℙ k V} (h : p ∈ pointsIn q.submodule) : p = q :=
  submodule_injective (Submodule.eq_of_le_of_finrank_eq h
    ((finrank_submodule p).trans (finrank_submodule q).symm))

@[expose] def line (p q : ℙ k V) : Submodule k V := p.submodule ⊔ q.submodule

theorem line_def (p q : ℙ k V) : line p q = p.submodule ⊔ q.submodule := rfl

theorem line_comm (p q : ℙ k V) : line p q = line q p := sup_comm _ _

theorem left_mem_pointsIn_line (p q : ℙ k V) : p ∈ pointsIn (line p q) :=
  mem_pointsIn.mpr le_sup_left

theorem right_mem_pointsIn_line (p q : ℙ k V) : q ∈ pointsIn (line p q) :=
  mem_pointsIn.mpr le_sup_right

theorem line_eq_span (p q : ℙ k V) : line p q = Submodule.span k {p.rep, q.rep} := by
  rw [line, submodule_eq, submodule_eq, Submodule.span_insert]

theorem line_le_iff {p q : ℙ k V} {W : Submodule k V} :
    line p q ≤ W ↔ p ∈ pointsIn W ∧ q ∈ pointsIn W :=
  sup_le_iff

instance (p q : ℙ k V) : FiniteDimensional k (line p q) := by
  rw [line_eq_span]
  exact FiniteDimensional.span_of_finite k (Set.toFinite _)

theorem finrank_line {p q : ℙ k V} (h : p ≠ q) : finrank k (line p q) = 2 := by
  rw [line_eq_span]
  have hli := linearIndependent_pair_iff_ne.mpr h
  rw [← Matrix.range_cons_cons_empty p.rep q.rep ![], finrank_span_eq_card hli]
  simp

theorem finrank_line_le (p q : ℙ k V) : finrank k (line p q) ≤ 2 := by
  by_cases h : p = q
  · subst h
    rw [line, sup_idem, finrank_submodule]
    omega
  · rw [finrank_line h]

theorem eq_line_of_mem {W : Submodule k V} (hW : finrank k W = 2) {p q : ℙ k V}
    (hp : p ∈ pointsIn W) (hq : q ∈ pointsIn W) (hpq : p ≠ q) : W = line p q := by
  have : FiniteDimensional k W := Module.finite_of_finrank_eq_succ hW
  exact (Submodule.eq_of_le_of_finrank_eq (line_le_iff.mpr ⟨hp, hq⟩)
    ((finrank_line hpq).trans hW.symm)).symm

theorem line_eq_of_mem {p q r : ℙ k V} (hpq : p ≠ q) (hr : r ∈ pointsIn (line p q))
    (hrp : r ≠ p) : line p r = line p q :=
  (eq_line_of_mem (finrank_line hpq) (left_mem_pointsIn_line p q) hr hrp.symm).symm

theorem line_eq_line_of_mem {p q x y : ℙ k V} (hpq : p ≠ q) (hxy : x ≠ y)
    (hx : x ∈ pointsIn (line p q)) (hy : y ∈ pointsIn (line p q)) :
    line x y = line p q :=
  (eq_line_of_mem (finrank_line hpq) hx hy hxy).symm

theorem finrank_line_sup {p q r : ℙ k V} (hpq : p ≠ q) (hr : r ∉ pointsIn (line p q)) :
    finrank k (line p q ⊔ r.submodule : Submodule k V) = 3 := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (line p q) r.submodule
  have hdisj : line p q ⊓ r.submodule = ⊥ := by
    rw [← disjoint_iff, submodule_eq, Submodule.disjoint_span_singleton]
    intro h
    exact absurd (rep_mem_iff_mem_pointsIn.mp h) hr
  rw [hdisj, finrank_bot, finrank_line hpq, finrank_submodule] at hsum
  omega

instance (p q r : ℙ k V) : FiniteDimensional k (line p q ⊔ r.submodule : Submodule k V) :=
  Submodule.finiteDimensional_sup _ _

theorem submodule_smul (g : V ≃ₗ[k] V) (p : ℙ k V) :
    (g • p).submodule = p.submodule.map (g : V →ₗ[k] V) := by
  induction p using Projectivization.ind with
  | h v hv => simp [submodule_mk, Submodule.map_span, Set.image_singleton]

theorem smul_mem_pointsIn_map {g : V ≃ₗ[k] V} {W : Submodule k V} {p : ℙ k V} :
    g • p ∈ pointsIn (W.map (g : V →ₗ[k] V)) ↔ p ∈ pointsIn W := by
  rw [mem_pointsIn, mem_pointsIn, submodule_smul]
  exact Submodule.map_le_map_iff_of_injective g.injective _ _

theorem smul_pointsIn (g : V ≃ₗ[k] V) (W : Submodule k V) :
    g • pointsIn W = pointsIn (W.map (g : V →ₗ[k] V)) := by
  ext q
  rw [← smul_inv_smul g q, Set.smul_mem_smul_set_iff, smul_mem_pointsIn_map]

theorem map_line (g : V ≃ₗ[k] V) (p q : ℙ k V) :
    (line p q).map (g : V →ₗ[k] V) = line (g • p) (g • q) := by
  rw [line, line, Submodule.map_sup, submodule_smul, submodule_smul]

theorem smul_pointsIn_line (g : V ≃ₗ[k] V) (p q : ℙ k V) :
    g • pointsIn (line p q) = pointsIn (line (g • p) (g • q)) := by
  rw [smul_pointsIn, map_line]

theorem smul_mem_pointsIn_line_iff {g : V ≃ₗ[k] V} {p q r : ℙ k V} :
    g • r ∈ pointsIn (line (g • p) (g • q)) ↔ r ∈ pointsIn (line p q) := by
  rw [← smul_pointsIn_line, Set.smul_mem_smul_set_iff]

theorem range_map_subtype (W : Submodule k V) :
    Set.range (Projectivization.map W.subtype W.injective_subtype) = pointsIn W := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Projectivization.ind with
    | h w hw =>
      rw [map_mk, mk_mem_pointsIn]
      exact w.2
  · intro hp
    induction p using Projectivization.ind with
    | h v hv =>
      rw [mk_mem_pointsIn] at hp
      refine ⟨mk k (⟨v, hp⟩ : W) (fun h => hv (congrArg Subtype.val h)), ?_⟩
      rw [map_mk]
      rfl

theorem ncard_pointsIn [Finite k] (W : Submodule k V) :
    (pointsIn W).ncard = ∑ i ∈ Finset.range (finrank k W), Nat.card k ^ i := by
  rw [← range_map_subtype, Set.ncard_range_of_injective (map_injective _ _),
    card_of_finrank k W rfl]

theorem ncard_pointsIn_of_finrank_two [Finite k] {W : Submodule k V} (hW : finrank k W = 2) :
    (pointsIn W).ncard = Nat.card k + 1 := by
  rw [ncard_pointsIn, hW]
  simp [Finset.sum_range_succ]
  ring

theorem ncard_pointsIn_line [Finite k] {p q : ℙ k V} (h : p ≠ q) :
    (pointsIn (line p q)).ncard = Nat.card k + 1 :=
  ncard_pointsIn_of_finrank_two (finrank_line h)

theorem ncard_pointsIn_of_finrank_three [Finite k] {W : Submodule k V} (hW : finrank k W = 3) :
    (pointsIn W).ncard = Nat.card k ^ 2 + Nat.card k + 1 := by
  rw [ncard_pointsIn, hW]
  simp [Finset.sum_range_succ]
  ring

theorem smul_eq_self_iff {g : V ≃ₗ[k] V} {p : ℙ k V} :
    g • p = p ↔ ∃ a : k, g p.rep = a • p.rep := by
  conv_lhs => rw [← mk_rep p]
  rw [smul_mk, mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, ha.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, ha.symm⟩

theorem smul_eq_self_of_three_fixed {g : V ≃ₗ[k] V} {p₁ p₂ p₃ q : ℙ k V} (h12 : p₁ ≠ p₂)
    (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃) (h3 : p₃ ∈ pointsIn (line p₁ p₂))
    (hg₁ : g • p₁ = p₁) (hg₂ : g • p₂ = p₂) (hg₃ : g • p₃ = p₃)
    (hq : q ∈ pointsIn (line p₁ p₂)) : g • q = q := by
  obtain ⟨a₁, ha₁⟩ := smul_eq_self_iff.mp hg₁
  obtain ⟨a₂, ha₂⟩ := smul_eq_self_iff.mp hg₂
  obtain ⟨a₃, ha₃⟩ := smul_eq_self_iff.mp hg₃
  have hli := LinearIndependent.pair_iff.mp (linearIndependent_pair_iff_ne.mpr h12)
  rw [← rep_mem_iff_mem_pointsIn, line_eq_span, Submodule.mem_span_pair] at h3 hq
  obtain ⟨s, t, hst⟩ := h3
  obtain ⟨c₁, c₂, hc⟩ := hq
  have hs : s ≠ 0 := by
    rintro rfl
    refine h23 (Eq.symm ?_)
    rw [← mk_rep p₂, ← mk_rep p₃, mk_eq_mk_iff']
    exact ⟨t, by rw [← hst, zero_smul, zero_add]⟩
  have ht : t ≠ 0 := by
    rintro rfl
    refine h13 (Eq.symm ?_)
    rw [← mk_rep p₁, ← mk_rep p₃, mk_eq_mk_iff']
    exact ⟨s, by rw [← hst, zero_smul, add_zero]⟩
  have key := hli (s * a₁ - a₃ * s) (t * a₂ - a₃ * t) (by
    have h := congrArg g hst
    rw [map_add, map_smul, map_smul, ha₁, ha₂, ha₃, ← hst, smul_add, smul_smul, smul_smul,
      smul_smul, smul_smul] at h
    rw [sub_smul, sub_smul]
    linear_combination (norm := module) h)
  have e1 : a₁ = a₃ := by
    have := key.1
    have : s * (a₁ - a₃) = 0 := by linear_combination this
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hs)
  have e2 : a₂ = a₃ := by
    have := key.2
    have : t * (a₂ - a₃) = 0 := by linear_combination this
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ht)
  rw [smul_eq_self_iff]
  refine ⟨a₃, ?_⟩
  have hrep : g q.rep = a₃ • q.rep := by
    rw [← hc, map_add, map_smul, map_smul, ha₁, ha₂, e1, e2, smul_add, smul_smul, smul_smul,
      smul_smul, smul_smul, mul_comm a₃ c₁, mul_comm a₃ c₂]
  exact hrep

theorem exists_mem_pointsIn_of_le_plane {E M D : Submodule k V} [FiniteDimensional k E]
    (hE : finrank k E = 3) (hM : finrank k M = 2) (hD : finrank k D = 2) (hME : M ≤ E)
    (hDE : D ≤ E) : ∃ r : ℙ k V, r ∈ pointsIn M ∧ r ∈ pointsIn D := by
  have : FiniteDimensional k M := Module.finite_of_finrank_eq_succ hM
  have : FiniteDimensional k D := Module.finite_of_finrank_eq_succ hD
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq M D
  have hle : finrank k (M ⊔ D : Submodule k V) ≤ 3 := hE ▸ Submodule.finrank_mono (sup_le hME hDE)
  have hne : M ⊓ D ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hsum
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨mk k v hv0, (mk_mem_pointsIn hv0).mpr hv.1, (mk_mem_pointsIn hv0).mpr hv.2⟩

end CFSG.ShultStronglyClosedTI.Singer

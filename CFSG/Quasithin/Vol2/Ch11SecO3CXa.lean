module

import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF.O3CX

variable {G : Type} [Group G]

abbrev cm (g h : G) : G := g * h * g⁻¹ * h⁻¹

abbrev qQ (W W' C : Subgroup G) : Subgroup G := W ⊓ C ⊔ W' ⊓ C

abbrev dQ (W W' C : Subgroup G) : Subgroup ↥(qQ W W' C) := (W ⊓ W').subgroupOf (qQ W W' C)

structure Frame (W W' C : Subgroup G) : Prop where
  cW : C ≤ Subgroup.normalizer (W : Set G)
  cW' : C ≤ Subgroup.normalizer (W' : Set G)
  wC : W ≤ Subgroup.normalizer (C : Set G)
  w'C : W' ≤ Subgroup.normalizer (C : Set G)
  ww : ∀ a ∈ W, ∀ b ∈ W, a * b * a⁻¹ * b⁻¹ ∈ W'
  w'w' : ∀ a ∈ W', ∀ b ∈ W', a * b * a⁻¹ * b⁻¹ ∈ W
  sqw : ∀ a ∈ W, a * a ∈ W'
  sqw' : ∀ a ∈ W', a * a ∈ W
  dC : W ⊓ W' ≤ C
  qq : ∀ a ∈ qQ W W' C, ∀ b ∈ qQ W W' C, a * b * a⁻¹ * b⁻¹ ∈ W ⊓ W'
  sqq : ∀ a ∈ qQ W W' C, a * a ∈ W ⊓ W'

variable {W W' C : Subgroup G}

namespace Frame

variable (hF : Frame W W' C)
include hF

theorem d_le_q : W ⊓ W' ≤ qQ W W' C := fun _ hd => Subgroup.mem_sup_left ⟨hd.1, hF.dC hd⟩

theorem conj_mem_D {q : G} (hq : q ∈ qQ W W' C) {d : G} (hd : d ∈ W ⊓ W') :
    q * d * q⁻¹ ∈ W ⊓ W' := by
  have h1 := hF.qq q hq d (hF.d_le_q hd)
  have : q * d * q⁻¹ = (q * d * q⁻¹ * d⁻¹) * d := by group
  rw [this]
  exact (W ⊓ W').mul_mem h1 hd

theorem dQ_normal : (dQ W W' C).Normal :=
  ⟨fun d hd q => by
    rw [Subgroup.mem_subgroupOf] at hd ⊢
    simpa using hF.conj_mem_D q.2 hd⟩

end Frame

structure Norm (W W' C : Subgroup G) (g : G) : Prop where
  q : ∀ q ∈ qQ W W' C, g * q * g⁻¹ ∈ qQ W W' C
  d : ∀ d ∈ W ⊓ W', g * d * g⁻¹ ∈ W ⊓ W'

@[expose] def conjQ {g : G} (hg : Norm W W' C g) : ↥(qQ W W' C) →* ↥(qQ W W' C) where
  toFun q := ⟨g * q * g⁻¹, hg.q q q.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem norm_mul {g h : G} (hg : Norm W W' C g) (hh : Norm W W' C h) : Norm W W' C (g * h) :=
  ⟨fun q hq => by simpa [mul_assoc] using hg.q _ (hh.q q hq),
    fun d hd => by simpa [mul_assoc] using hg.d _ (hh.d d hd)⟩

abbrev QS (W W' C : Subgroup G) [(dQ W W' C).Normal] : Type :=
  ↥(qQ W W' C) ⧸ dQ W W' C

section Act

variable [(dQ W W' C).Normal]

abbrev qc (q : G) (hq : q ∈ qQ W W' C) : QS W W' C := QuotientGroup.mk ⟨q, hq⟩

abbrev qA (W W' C : Subgroup G) [(dQ W W' C).Normal] (a : G) (ha : a ∈ W ⊓ C) : QS W W' C :=
  qc a (Subgroup.mem_sup_left ha)

abbrev qB (W W' C : Subgroup G) [(dQ W W' C).Normal] (b : G) (hb : b ∈ W' ⊓ C) : QS W W' C :=
  qc b (Subgroup.mem_sup_right hb)

theorem qc_eq_one_iff {q : G} (hq : q ∈ qQ W W' C) : qc q hq = 1 ↔ q ∈ W ⊓ W' := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem qc_mul {a b : G} (ha : a ∈ qQ W W' C) (hb : b ∈ qQ W W' C) :
    qc a ha * qc b hb = qc (a * b) ((qQ W W' C).mul_mem ha hb) := rfl

theorem qc_eq_qc_iff {a b : G} (ha : a ∈ qQ W W' C) (hb : b ∈ qQ W W' C) :
    qc a ha = qc b hb ↔ a⁻¹ * b ∈ W ⊓ W' := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

@[expose] noncomputable def act {g : G} (hg : Norm W W' C g) : QS W W' C →* QS W W' C :=
  QuotientGroup.map (dQ W W' C) (dQ W W' C) (conjQ hg) fun d hd => by
    rw [Subgroup.mem_subgroupOf] at hd
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hg.d d hd

theorem act_qc {g : G} (hg : Norm W W' C g) {q : G} (hq : q ∈ qQ W W' C) :
    act hg (qc q hq) = qc (g * q * g⁻¹) (hg.q q hq) := rfl

theorem act_mul {g h : G} (hg : Norm W W' C g) (hh : Norm W W' C h) (v : QS W W' C) :
    act (norm_mul hg hh) v = act hg (act hh v) := by
  induction v using QuotientGroup.induction_on with
  | H q =>
    change act (norm_mul hg hh) (qc q q.2) = act hg (act hh (qc q q.2))
    rw [act_qc, act_qc, act_qc]
    congr 1
    group

theorem act_congr {g h : G} (hg : Norm W W' C g) (hh : Norm W W' C h) (e : g = h)
    (v : QS W W' C) : act hg v = act hh v := by
  subst e
  rfl

end Act

end CFSG.Quasithin.Vol2.Ch11.SecF.O3CX

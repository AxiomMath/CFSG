module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.RonanF95

open scoped Pointwise

variable {G : Type*} [Group G]

structure FormHyp (V₁ P : Subgroup G) : Prop where
  card : Nat.card V₁ = 2
  le : V₁ ≤ P
  central : ∀ z ∈ V₁, ∀ p ∈ P, p * z = z * p
  sq : ∀ p ∈ P, p * p ∈ V₁
  comm : ∀ p ∈ P, ∀ r ∈ P, p * r * p⁻¹ * r⁻¹ ∈ V₁

variable {V₁ P : Subgroup G}

open Classical in
noncomputable def ind2 (c : G) : ZMod 2 := if c = 1 then 0 else 1

theorem ind2_one : ind2 (1 : G) = 0 := by
  simp [ind2]

theorem ind2_of_ne {c : G} (hc : c ≠ 1) : ind2 c = 1 := by
  simp [ind2, hc]

theorem ind2_conj (w c : G) : ind2 (w * c * w⁻¹) = ind2 c := by
  by_cases h : c = 1
  · simp [ind2, h]
  · have h' : ¬ (w * c * w⁻¹ = 1) := fun h2 => h (conj_eq_one_iff.mp h2)
    simp [ind2, h, h']

theorem FormHyp.sq_eq_one_of_mem (hP : FormHyp V₁ P) {z : G} (hz : z ∈ V₁) : z * z = 1 := by
  have h := congrArg Subtype.val (pow_card_eq_one' (G := V₁) (x := ⟨z, hz⟩))
  rw [hP.card] at h
  simpa [pow_two] using h

theorem FormHyp.eq_of_ne_one (hP : FormHyp V₁ P) {c₁ c₂ : G} (h₁ : c₁ ∈ V₁) (h₂ : c₂ ∈ V₁)
    (hc₁ : c₁ ≠ 1) (hc₂ : c₂ ≠ 1) : c₁ = c₂ := by
  obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.mp hP.card
  have key : ∀ c : V₁, c = x ∨ c = y := fun c => by
    have hc : c ∈ ({x, y} : Set V₁) := by
      rw [hset]
      exact Set.mem_univ c
    simpa using hc
  have n1 : (⟨c₁, h₁⟩ : V₁) ≠ 1 := fun h => hc₁ (congrArg Subtype.val h)
  have n2 : (⟨c₂, h₂⟩ : V₁) ≠ 1 := fun h => hc₂ (congrArg Subtype.val h)
  have e : (⟨c₁, h₁⟩ : V₁) = ⟨c₂, h₂⟩ := by
    rcases key 1 with h0 | h0 <;> rcases key ⟨c₁, h₁⟩ with h1 | h1 <;>
      rcases key ⟨c₂, h₂⟩ with h2 | h2 <;> simp_all
  exact congrArg Subtype.val e

theorem FormHyp.ind2_mul (hP : FormHyp V₁ P) {c₁ c₂ : G} (h₁ : c₁ ∈ V₁) (h₂ : c₂ ∈ V₁) :
    ind2 (c₁ * c₂) = ind2 c₁ + ind2 c₂ := by
  by_cases e1 : c₁ = 1
  · rw [e1, one_mul, ind2_one, zero_add]
  by_cases e2 : c₂ = 1
  · rw [e2, mul_one, ind2_one, add_zero]
  rw [← hP.eq_of_ne_one h₁ h₂ e1 e2, hP.sq_eq_one_of_mem h₁, ind2_one, ind2_of_ne e1] <;> decide

theorem FormHyp.conj_eq_of_mem (hP : FormHyp V₁ P) {z r : G} (hz : z ∈ V₁) (hr : r ∈ P) :
    z * r * z⁻¹ = r := by
  rw [mul_inv_eq_iff_eq_mul]
  exact (hP.central z hz r hr).symm

theorem FormHyp.conj_mem_eq (hP : FormHyp V₁ P) {u a : G} (hu : u ∈ V₁) (ha : a ∈ P) :
    a * u * a⁻¹ = u := by
  rw [mul_inv_eq_iff_eq_mul]
  exact hP.central u hu a ha

theorem FormHyp.shift_left (hP : FormHyp V₁ P) {a z r : G} (hz : z ∈ V₁) (hr : r ∈ P) :
    a * z * r * (a * z)⁻¹ * r⁻¹ = a * r * a⁻¹ * r⁻¹ := by
  have h := hP.conj_eq_of_mem hz hr
  calc a * z * r * (a * z)⁻¹ * r⁻¹ = a * (z * r * z⁻¹) * a⁻¹ * r⁻¹ := by group
    _ = a * r * a⁻¹ * r⁻¹ := by rw [h]

theorem FormHyp.shift_right (hP : FormHyp V₁ P) {p z r : G} (hz : z ∈ V₁) (hp : p ∈ P) :
    p * (r * z) * p⁻¹ * (r * z)⁻¹ = p * r * p⁻¹ * r⁻¹ := by
  have h := hP.conj_eq_of_mem hz (P.inv_mem hp)
  calc p * (r * z) * p⁻¹ * (r * z)⁻¹ = p * r * (z * p⁻¹ * z⁻¹) * r⁻¹ := by group
    _ = p * r * p⁻¹ * r⁻¹ := by rw [h]

theorem FormHyp.qf_compat (hP : FormHyp V₁ P) (a b : P) (hab : a⁻¹ * b ∈ V₁.subgroupOf P) :
    ind2 ((a : G) * a) = ind2 ((b : G) * b) := by
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hab
  obtain ⟨z, hz, hbz⟩ : ∃ z ∈ V₁, (b : G) = (a : G) * z :=
    ⟨(a : G)⁻¹ * (b : G), hab, by group⟩
  have hc : (a : G) * z = z * a := hP.central z hz a a.2
  have hbb : (b : G) * b = (a : G) * a := by
    rw [hbz]
    calc (a : G) * z * ((a : G) * z) = (a : G) * (z * (a : G)) * z := by group
      _ = (a : G) * ((a : G) * z) * z := by rw [← hc]
      _ = (a : G) * (a : G) * (z * z) := by group
      _ = (a : G) * (a : G) := by rw [hP.sq_eq_one_of_mem hz, mul_one]
  rw [hbb]

theorem FormHyp.bf_compat (hP : FormHyp V₁ P) (a₁ a₂ b₁ b₂ : P)
    (h₁ : a₁⁻¹ * b₁ ∈ V₁.subgroupOf P) (h₂ : a₂⁻¹ * b₂ ∈ V₁.subgroupOf P) :
    ind2 ((a₁ : G) * a₂ * (a₁ : G)⁻¹ * (a₂ : G)⁻¹) =
      ind2 ((b₁ : G) * b₂ * (b₁ : G)⁻¹ * (b₂ : G)⁻¹) := by
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h₁ h₂
  obtain ⟨z₁, hz₁, hb₁⟩ : ∃ z ∈ V₁, (b₁ : G) = (a₁ : G) * z :=
    ⟨(a₁ : G)⁻¹ * (b₁ : G), h₁, by group⟩
  obtain ⟨z₂, hz₂, hb₂⟩ : ∃ z ∈ V₁, (b₂ : G) = (a₂ : G) * z :=
    ⟨(a₂ : G)⁻¹ * (b₂ : G), h₂, by group⟩
  have e1 : (b₁ : G) * b₂ * (b₁ : G)⁻¹ * (b₂ : G)⁻¹ =
      (a₁ : G) * b₂ * (a₁ : G)⁻¹ * (b₂ : G)⁻¹ := by
    rw [hb₁]
    exact hP.shift_left hz₁ b₂.2
  have e2 : (a₁ : G) * b₂ * (a₁ : G)⁻¹ * (b₂ : G)⁻¹ =
      (a₁ : G) * a₂ * (a₁ : G)⁻¹ * (a₂ : G)⁻¹ := by
    rw [hb₂]
    exact hP.shift_right hz₂ a₁.2
  rw [e1, e2]

theorem FormHyp.normal (hP : FormHyp V₁ P) : (V₁.subgroupOf P).Normal := by
  refine ⟨fun n hn g => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hn ⊢
  rw [hP.conj_mem_eq hn g.2]
  exact hn

abbrev Ebar (V₁ P : Subgroup G) [(V₁.subgroupOf P).Normal] : Type _ := ↥P ⧸ V₁.subgroupOf P

namespace FormHyp

variable [(V₁.subgroupOf P).Normal]

@[expose, instance_reducible] noncomputable def commGroup (_hP : FormHyp V₁ P) : CommGroup (Ebar V₁ P) :=
  { (inferInstance : Group (Ebar V₁ P)) with
    mul_comm := fun x y => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      have key : ((a : G) * b)⁻¹ * ((b : G) * a) =
          (b : G)⁻¹ * (a : G)⁻¹ * ((b : G)⁻¹)⁻¹ * ((a : G)⁻¹)⁻¹ := by group
      rw [key]
      exact _hP.comm _ (P.inv_mem b.2) _ (P.inv_mem a.2) }

theorem exp (_hP : FormHyp V₁ P) (x : Ebar V₁ P) : x * x = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  exact _hP.sq _ a.2

theorem finite [Finite G] (_hP : FormHyp V₁ P) : Finite (Ebar V₁ P) := inferInstance

@[expose] noncomputable def qf (_hP : FormHyp V₁ P) : Ebar V₁ P → ZMod 2 :=
  Quotient.lift (fun p : P => ind2 ((p : G) * p))
    (fun a b hab => _hP.qf_compat a b (QuotientGroup.leftRel_apply.mp hab))

@[expose] noncomputable def bf (_hP : FormHyp V₁ P) : Ebar V₁ P → Ebar V₁ P → ZMod 2 :=
  Quotient.lift₂ (fun p r : P => ind2 ((p : G) * r * (p : G)⁻¹ * (r : G)⁻¹))
    (fun _ _ _ _ h₁ h₂ => _hP.bf_compat _ _ _ _
      (QuotientGroup.leftRel_apply.mp h₁) (QuotientGroup.leftRel_apply.mp h₂))

open Classical in
theorem qf_mk (hP : FormHyp V₁ P) (p : ↥P) :
    hP.qf (QuotientGroup.mk p) = if (p : G) * p = 1 then 0 else 1 := by
  rfl

open Classical in
theorem bf_mk (hP : FormHyp V₁ P) (p r : ↥P) :
    hP.bf (QuotientGroup.mk p) (QuotientGroup.mk r) =
      if (p : G) * r * (p : G)⁻¹ * (r : G)⁻¹ = 1 then 0 else 1 := by
  rfl

theorem bf_left (hP : FormHyp V₁ P) (x y z : Ebar V₁ P) :
    hP.bf (x * y) z = hP.bf x z + hP.bf y z := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective z
  rw [← QuotientGroup.mk_mul]
  show ind2 ((a : G) * b * c * ((a : G) * b)⁻¹ * (c : G)⁻¹) =
    ind2 ((a : G) * c * (a : G)⁻¹ * (c : G)⁻¹) + ind2 ((b : G) * c * (b : G)⁻¹ * (c : G)⁻¹)
  have hu : (b : G) * c * (b : G)⁻¹ * (c : G)⁻¹ ∈ V₁ := hP.comm _ b.2 _ c.2
  have hv : (a : G) * c * (a : G)⁻¹ * (c : G)⁻¹ ∈ V₁ := hP.comm _ a.2 _ c.2
  have hid : (a : G) * b * c * ((a : G) * b)⁻¹ * (c : G)⁻¹ =
      (a : G) * ((b : G) * c * (b : G)⁻¹ * (c : G)⁻¹) * (a : G)⁻¹ *
        ((a : G) * c * (a : G)⁻¹ * (c : G)⁻¹) := by group
  rw [hid, hP.conj_mem_eq hu a.2, hP.ind2_mul hu hv]
  exact add_comm _ _

theorem bf_right (hP : FormHyp V₁ P) (x y z : Ebar V₁ P) :
    hP.bf x (y * z) = hP.bf x y + hP.bf x z := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective z
  rw [← QuotientGroup.mk_mul]
  show ind2 ((a : G) * ((b : G) * c) * (a : G)⁻¹ * ((b : G) * c)⁻¹) =
    ind2 ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) + ind2 ((a : G) * c * (a : G)⁻¹ * (c : G)⁻¹)
  have ht : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ V₁ := hP.comm _ a.2 _ b.2
  have hv : (a : G) * c * (a : G)⁻¹ * (c : G)⁻¹ ∈ V₁ := hP.comm _ a.2 _ c.2
  have hid : (a : G) * ((b : G) * c) * (a : G)⁻¹ * ((b : G) * c)⁻¹ =
      ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) *
        ((b : G) * ((a : G) * c * (a : G)⁻¹ * (c : G)⁻¹) * (b : G)⁻¹) := by group
  rw [hid, hP.conj_mem_eq hv b.2, hP.ind2_mul ht hv]

theorem bf_alt (hP : FormHyp V₁ P) (x : Ebar V₁ P) : hP.bf x x = 0 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  show ind2 ((a : G) * a * (a : G)⁻¹ * (a : G)⁻¹) = 0
  have h1 : (a : G) * a * (a : G)⁻¹ * (a : G)⁻¹ = 1 := by group
  rw [h1, ind2_one]

theorem qf_mul (hP : FormHyp V₁ P) (x y : Ebar V₁ P) :
    hP.qf (x * y) = hP.qf x + hP.qf y + hP.bf x y := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul]
  show ind2 ((a : G) * b * ((a : G) * b)) =
    ind2 ((a : G) * a) + ind2 ((b : G) * b) + ind2 ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹)
  have hc : (b : G) * ((a : G) * a) = ((a : G) * a) * b :=
    hP.central _ (hP.sq _ a.2) _ b.2
  have hid : (a : G) * b * ((a : G) * b) =
      ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) * ((a : G) * a) * ((b : G) * b) := by
    calc (a : G) * b * ((a : G) * b)
        = ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) * (b * ((a : G) * a)) * b := by group
      _ = ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) * (((a : G) * a) * b) * b := by rw [hc]
      _ = ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) * ((a : G) * a) * ((b : G) * b) := by group
  have ht : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ V₁ := hP.comm _ a.2 _ b.2
  have ha2 : (a : G) * a ∈ V₁ := hP.sq _ a.2
  have hb2 : (b : G) * b ∈ V₁ := hP.sq _ b.2
  rw [hid, hP.ind2_mul (V₁.mul_mem ht ha2) hb2, hP.ind2_mul ht ha2]
  ring

@[expose] noncomputable def conjE (_hP : FormHyp V₁ P) (w : G) (hw : ∀ p ∈ P, w * p * w⁻¹ ∈ P)
    (hw' : ∀ p ∈ P, w⁻¹ * p * w ∈ P) (hw₁ : ∀ z ∈ V₁, w * z * w⁻¹ = z) :
    Ebar V₁ P ≃* Ebar V₁ P :=
  QuotientGroup.congr (V₁.subgroupOf P) (V₁.subgroupOf P)
    { toFun := fun p => ⟨w * p * w⁻¹, hw p p.2⟩
      invFun := fun p => ⟨w⁻¹ * p * w, hw' p p.2⟩
      left_inv := fun p => Subtype.ext (by
        show w⁻¹ * (w * (p : G) * w⁻¹) * w = p
        group)
      right_inv := fun p => Subtype.ext (by
        show w * (w⁻¹ * (p : G) * w) * w⁻¹ = p
        group)
      map_mul' := fun p q => Subtype.ext (by
        show w * ((p : G) * q) * w⁻¹ = (w * p * w⁻¹) * (w * q * w⁻¹)
        group) }
    (by
      have hinv : ∀ z ∈ V₁, w⁻¹ * z * w = z := by
        intro z hz
        have h := hw₁ z hz
        rw [mul_inv_eq_iff_eq_mul] at h
        rw [mul_assoc, ← h, inv_mul_cancel_left]
      ext q
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        show w * (x : G) * w⁻¹ ∈ V₁
        rw [hw₁ _ hx]
        exact hx
      · intro hq
        have hq' : (q : G) ∈ V₁ := Subgroup.mem_subgroupOf.mp hq
        refine ⟨⟨w⁻¹ * q * w, hw' q q.2⟩, ?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf]
          show w⁻¹ * (q : G) * w ∈ V₁
          rw [hinv _ hq']
          exact hq'
        · exact Subtype.ext (by
            show w * (w⁻¹ * (q : G) * w) * w⁻¹ = q
            group))

theorem conjE_mk (hP : FormHyp V₁ P) (w : G) (hw : ∀ p ∈ P, w * p * w⁻¹ ∈ P)
    (hw' : ∀ p ∈ P, w⁻¹ * p * w ∈ P) (hw₁ : ∀ z ∈ V₁, w * z * w⁻¹ = z) (p : ↥P) :
    hP.conjE w hw hw' hw₁ (QuotientGroup.mk p) =
      QuotientGroup.mk ⟨w * p * w⁻¹, hw p p.2⟩ := by
  rfl

theorem qf_conjE (hP : FormHyp V₁ P) (w : G) (hw : ∀ p ∈ P, w * p * w⁻¹ ∈ P)
    (hw' : ∀ p ∈ P, w⁻¹ * p * w ∈ P) (hw₁ : ∀ z ∈ V₁, w * z * w⁻¹ = z) (x : Ebar V₁ P) :
    hP.qf (hP.conjE w hw hw' hw₁ x) = hP.qf x := by
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
  rw [conjE_mk]
  show ind2 (w * (p : G) * w⁻¹ * (w * (p : G) * w⁻¹)) = ind2 ((p : G) * p)
  have key : w * (p : G) * w⁻¹ * (w * (p : G) * w⁻¹) = w * ((p : G) * p) * w⁻¹ := by group
  rw [key, ind2_conj]

@[expose] noncomputable def imgE (V₁ P : Subgroup G) [(V₁.subgroupOf P).Normal] (Y : Subgroup G) :
    Subgroup (Ebar V₁ P) :=
  (Y.subgroupOf P).map (QuotientGroup.mk' (V₁.subgroupOf P))

theorem mem_imgE {Y : Subgroup G} (hY : V₁ ≤ Y) (p : ↥P) :
    (QuotientGroup.mk p : Ebar V₁ P) ∈ imgE V₁ P Y ↔ (p : G) ∈ Y := by
  unfold imgE
  constructor
  · intro h
    obtain ⟨x, hx, hxp⟩ := Subgroup.mem_map.mp h
    rw [QuotientGroup.mk'_apply] at hxp
    rw [Subgroup.mem_subgroupOf] at hx
    have h2 := QuotientGroup.eq.mp hxp
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    have h4 := Y.mul_mem hx (hY h2)
    simpa using h4
  · intro hp
    exact Subgroup.mem_map.mpr ⟨p, Subgroup.mem_subgroupOf.mpr hp, rfl⟩

theorem card_imgE_mul {Y : Subgroup G} (hY : V₁ ≤ Y) (hYP : Y ≤ P) :
    Nat.card V₁ * Nat.card (imgE V₁ P Y) = Nat.card Y := by
  have hVP : V₁ ≤ P := hY.trans hYP
  have hsub : V₁.subgroupOf P ≤ Y.subgroupOf P := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hY (Subgroup.mem_subgroupOf.mp hx))
  let f : (Y.subgroupOf P) →* Ebar V₁ P :=
    (QuotientGroup.mk' (V₁.subgroupOf P)).comp (Y.subgroupOf P).subtype
  have hrange : f.range = imgE V₁ P Y := by
    unfold imgE
    ext q
    constructor
    · intro hq
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hq
      exact Subgroup.mem_map.mpr ⟨(x : P), x.2, rfl⟩
    · intro hq
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq
      exact MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
  have hker : f.ker = (V₁.subgroupOf P).subgroupOf (Y.subgroupOf P) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk (x : P) : Ebar V₁ P) = 1 ↔ (x : P) ∈ V₁.subgroupOf P
    rw [QuotientGroup.eq_one_iff]
  have c1 : Nat.card ((V₁.subgroupOf P).subgroupOf (Y.subgroupOf P)) = Nat.card V₁ :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsub).toEquiv).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVP).toEquiv)
  have c3 : Nat.card (Y.subgroupOf P) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYP).toEquiv
  have hidx : Nat.card f.ker * f.ker.index = Nat.card (Y.subgroupOf P) :=
    Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hrange, hker, c1, c3] at hidx
  exact hidx

theorem card_imgE (hP : FormHyp V₁ P) {Y : Subgroup G} (hY : V₁ ≤ Y) (hYP : Y ≤ P) :
    Nat.card (imgE V₁ P Y) * 2 = Nat.card Y := by
  have h := card_imgE_mul hY hYP
  rw [hP.card] at h
  omega

end FormHyp

end CFSG.Quasithin.RonanF95

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
public import Mathlib.GroupTheory.Commutator.Finite
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.Quasithin.C48Cover

open scoped commutatorElement

abbrev Z4C := Multiplicative (Fin 3 → ZMod 4)

namespace Z4C

theorem pow_four (a : Z4C) : a ^ 4 = 1 := by
  revert a
  decide

theorem exists_sq_eq (a : Z4C) (h : a ^ 2 = 1) : ∃ b : Z4C, b ^ 2 = a := by
  revert a
  decide

theorem card_inv : Fintype.card {a : Z4C // a ^ 2 = 1 ∧ a ≠ 1} = 7 := by
  decide

@[expose] def y8 : List Z4C := [Multiplicative.ofAdd ![0, 0, 0], Multiplicative.ofAdd ![2, 0, 0],
  Multiplicative.ofAdd ![0, 2, 0], Multiplicative.ofAdd ![0, 0, 2], Multiplicative.ofAdd ![2, 2, 0],
  Multiplicative.ofAdd ![2, 0, 2], Multiplicative.ofAdd ![0, 2, 2], Multiplicative.ofAdd ![2, 2, 2]]

theorem mem_y8 : ∀ x : Z4C, x ^ 2 = 1 → x ∈ y8 := by
  decide

@[expose] def spanOK (a b c : Z4C) : Bool :=
  !(a != 1 && b != 1 && b != a && c != 1 && c != a && c != b && c != a * b) ||
  y8.all fun d => [false, true].any fun i => [false, true].any fun j => [false, true].any fun k =>
    d == (bif i then a else 1) * (bif j then b else 1) * (bif k then c else 1)

theorem spanOK_all : y8.all (fun a => y8.all fun b => y8.all fun c => spanOK a b c) = true := by
  decide

theorem span_three {a b c d : Z4C} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hd : d ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hc1 : c ≠ 1) (hca : c ≠ a)
    (hcb : c ≠ b) (hcab : c ≠ a * b) :
    ∃ i j k : Bool, d = (bif i then a else 1) * (bif j then b else 1) * (bif k then c else 1) := by
  have h := spanOK_all
  simp only [List.all_eq_true] at h
  have h1 := h a (mem_y8 a ha) b (mem_y8 b hb) c (mem_y8 c hc)
  simp only [spanOK, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_iff,
    bne_eq_false_iff_eq, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · exfalso
    tauto
  · obtain ⟨i, -, j, -, k, -, hijk⟩ := h1 d (mem_y8 d hd)
    exact ⟨i, j, k, hijk⟩

theorem exists_ne_four : ∀ a c : {x : Z4C // x ^ 2 = 1}, ∃ b : {x : Z4C // x ^ 2 = 1},
    (b : Z4C) ≠ 1 ∧ (b : Z4C) ≠ a ∧ (b : Z4C) ≠ c ∧ (b : Z4C) ≠ a * c := by
  decide

theorem fix_of_pow_fix (φ : MulAut Z4C) (hφ : φ ^ 7 = 1) {a : Z4C} {d : ℕ} (hd0 : 0 < d)
    (hd7 : d < 7) (h : (φ ^ d) a = a) : φ a = a := by
  have hfix : ∀ m : ℕ, ((φ ^ d) ^ m) a = a := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ, MulAut.mul_apply, h, ih]
  have key : ∀ m q : ℕ, d * m = 7 * q + 1 → φ a = a := by
    intro m q hm
    have : φ = (φ ^ d) ^ m := by
      rw [← pow_mul, hm, pow_succ, pow_mul, hφ, one_pow, one_mul]
    rw [this]
    exact hfix m
  interval_cases d
  · simpa using h
  · exact key 4 1 rfl
  · exact key 5 2 rfl
  · exact key 2 1 rfl
  · exact key 3 2 rfl
  · exact key 6 5 rfl

@[expose] def orbitMap (φ : MulAut Z4C) {a : Z4C} (ha : a ^ 2 = 1) (ha1 : a ≠ 1) :
    Fin 7 → {b : Z4C // b ^ 2 = 1 ∧ b ≠ 1} := fun k =>
  ⟨(φ ^ (k : ℕ)) a, by rw [← map_pow, ha, map_one], fun h => ha1 (by
    have := congrArg (φ ^ (k : ℕ)).symm h
    simpa using this)⟩

theorem fix_of_not_injective (φ : MulAut Z4C) (hφ : φ ^ 7 = 1) {a : Z4C} (ha : a ^ 2 = 1)
    (ha1 : a ≠ 1) (h : ¬ Function.Injective (orbitMap φ ha ha1)) : φ a = a := by
  simp only [Function.Injective, not_forall] at h
  obtain ⟨i, j, hij, hne⟩ := h
  have hval : (φ ^ (i : ℕ)) a = (φ ^ (j : ℕ)) a := congrArg Subtype.val hij
  rcases Nat.lt_or_gt_of_ne (fun e => hne (Fin.ext e)) with hlt | hlt
  · refine fix_of_pow_fix φ hφ (d := (j : ℕ) - i) (by omega) (by omega) ?_
    have : (φ ^ (j : ℕ)) a = (φ ^ (i : ℕ)) ((φ ^ ((j : ℕ) - i)) a) := by
      rw [← MulAut.mul_apply, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [this] at hval
    exact ((φ ^ (i : ℕ)).injective hval).symm
  · refine fix_of_pow_fix φ hφ (d := (i : ℕ) - j) (by omega) (by omega) ?_
    have : (φ ^ (i : ℕ)) a = (φ ^ (j : ℕ)) ((φ ^ ((i : ℕ) - j)) a) := by
      rw [← MulAut.mul_apply, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [this] at hval
    exact (φ ^ (j : ℕ)).injective hval

theorem surjective_of_injective (φ : MulAut Z4C) {a : Z4C} (ha : a ^ 2 = 1) (ha1 : a ≠ 1)
    (h : Function.Injective (orbitMap φ ha ha1)) : Function.Surjective (orbitMap φ ha ha1) :=
  ((Fintype.bijective_iff_injective_and_card _).2 ⟨h, by rw [card_inv, Fintype.card_fin]⟩).2

theorem eq_one_of_fix (φ : MulAut Z4C) (hφ : φ ^ 7 = 1) {a₀ : Z4C} (ha₀ : a₀ ^ 2 = 1)
    (ha₀1 : a₀ ≠ 1) (hfix : φ a₀ = a₀) : φ = 1 := by
  have hinv : ∀ y : Z4C, y ^ 2 = 1 → φ y = y := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1, map_one]
    by_cases hinj : Function.Injective (orbitMap φ hy hy1)
    · obtain ⟨k, hk⟩ := surjective_of_injective φ hy hy1 hinj ⟨a₀, ha₀, ha₀1⟩
      have hk' : (φ ^ (k : ℕ)) y = a₀ := congrArg Subtype.val hk
      have hfixk : (φ ^ (k : ℕ)) a₀ = a₀ := by
        induction (k : ℕ) with
        | zero => rfl
        | succ m ih => rw [pow_succ, MulAut.mul_apply, hfix, ih]
      have : y = a₀ := (φ ^ (k : ℕ)).injective (hk'.trans hfixk.symm)
      rw [this, hfix]
    · exact fix_of_not_injective φ hφ hy hy1 hinj
  refine MulEquiv.ext fun n => ?_
  set y := n⁻¹ * φ n with hy
  have hn2 : φ (n ^ 2) = n ^ 2 := hinv _ (by rw [← pow_mul, pow_four])
  have hy2 : y ^ 2 = 1 := by
    have : (n * y) ^ 2 = n ^ 2 := by
      rw [hy, mul_inv_cancel_left, ← map_pow, hn2]
    rw [mul_pow] at this
    exact mul_left_cancel (this.trans (mul_one _).symm)
  have hφy : φ y = y := hinv y hy2
  have hφn : φ n = n * y := by rw [hy, mul_inv_cancel_left]
  have hiter : ∀ k : ℕ, (φ ^ k) n = n * y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hφy, hφn, mul_assoc, ← pow_succ']
  have h7 := hiter 7
  rw [hφ, MulAut.one_apply] at h7
  have hy7 : y ^ 7 = 1 := mul_left_cancel (h7.symm.trans (mul_one n).symm)
  have hy1 : y = 1 := by
    have : y ^ 7 = y * (y ^ 2) ^ 3 := by rw [← pow_mul, ← pow_succ']
    rw [this, hy2, one_pow, mul_one] at hy7
    exact hy7
  show φ n = n
  rw [hφn, hy1, mul_one]

theorem exists_pow_eq (φ : MulAut Z4C) (hφ : φ ^ 7 = 1) (hφ1 : φ ≠ 1) {a b : Z4C}
    (ha : a ^ 2 = 1) (ha1 : a ≠ 1) (hb : b ^ 2 = 1) (hb1 : b ≠ 1) :
    ∃ k : ℕ, (φ ^ k) a = b := by
  have hinj : Function.Injective (orbitMap φ ha ha1) := by
    by_contra h
    exact hφ1 (eq_one_of_fix φ hφ ha ha1 (fix_of_not_injective φ hφ ha ha1 h))
  obtain ⟨k, hk⟩ := surjective_of_injective φ ha ha1 hinj ⟨b, hb, hb1⟩
  exact ⟨k, congrArg Subtype.val hk⟩

end Z4C

section Core

variable {Q : Type} [Group Q] [Finite Q]

theorem sq_eq_one_of_card_le_two {H : Subgroup Q} (hH : Nat.card H ≤ 2) {z : Q} (hz : z ∈ H) :
    z ^ 2 = 1 := by
  have h := pow_card_eq_one' (G := ↥H) (x := ⟨z, hz⟩)
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hz' : (⟨z, hz⟩ : ↥H) ^ 2 = 1 := by
    rcases (by omega : Nat.card H = 1 ∨ Nat.card H = 2) with h1 | h2
    · rw [h1, pow_one] at h
      rw [h, one_pow]
    · rwa [h2] at h
  exact congrArg Subtype.val hz'

theorem eq_of_ne_one_of_card_le_two {H : Subgroup Q} (hH : Nat.card H ≤ 2) {a b : Q}
    (ha : a ∈ H) (hb : b ∈ H) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  by_contra hab
  have hinj : Function.Injective (![⟨1, H.one_mem⟩, ⟨a, ha⟩, ⟨b, hb⟩] : Fin 3 → ↥H) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Subtype.ext_iff, eq_comm]
  have := Nat.card_le_card_of_injective _ hinj
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

omit [Finite Q] in
theorem commutator_mul_right {x u u' : Q} (hu' : ⁅x, u'⁆ ∈ Subgroup.center Q) :
    ⁅x, u * u'⁆ = ⁅x, u⁆ * ⁅x, u'⁆ := by
  have e1 : x * u * x⁻¹ = ⁅x, u⁆ * u := by rw [commutatorElement_def]; group
  have e2 : x * u' * x⁻¹ = ⁅x, u'⁆ * u' := by rw [commutatorElement_def]; group
  have hc := Subgroup.mem_center_iff.mp hu'
  have e0 : ⁅x, u * u'⁆ = (x * u * x⁻¹) * (x * u' * x⁻¹) * u'⁻¹ * u⁻¹ := by
    rw [commutatorElement_def]; group
  rw [e0, e1, e2]
  generalize ⁅x, u⁆ = c₁ at *
  generalize ⁅x, u'⁆ = c₂ at *
  rw [show c₁ * u * (c₂ * u') * u'⁻¹ * u⁻¹ = c₁ * (u * c₂) * u⁻¹ by group, hc u]
  group

omit [Finite Q] in
theorem commutator_mul_left {x x' u : Q} (hx' : ⁅x', u⁆ ∈ Subgroup.center Q) :
    ⁅x * x', u⁆ = ⁅x, u⁆ * ⁅x', u⁆ := by
  have e1 : x * u * x⁻¹ * u⁻¹ = ⁅x, u⁆ := by rw [commutatorElement_def]
  have e2 : x' * u * x'⁻¹ = ⁅x', u⁆ * u := by rw [commutatorElement_def]; group
  have hc := Subgroup.mem_center_iff.mp hx'
  have e0 : ⁅x * x', u⁆ = x * (x' * u * x'⁻¹) * x⁻¹ * u⁻¹ := by
    rw [commutatorElement_def]; group
  rw [e0, e2]
  have e3 : x * (⁅x', u⁆ * u) * x⁻¹ * u⁻¹ = ⁅x', u⁆ * (x * u * x⁻¹ * u⁻¹) := by
    rw [show x * (⁅x', u⁆ * u) * x⁻¹ * u⁻¹ = (x * ⁅x', u⁆) * u * x⁻¹ * u⁻¹ by group, hc x]
    group
  rw [e3, e1]
  exact (Subgroup.mem_center_iff.mp hx' _).symm

variable {N : Subgroup (Q ⧸ Subgroup.center Q)}

@[expose] noncomputable def zα (e : ↥N ≃* Z4C) :
    ↥(N.comap (QuotientGroup.mk' (Subgroup.center Q))) →* Z4C :=
  e.toMonoidHom.comp ((((QuotientGroup.mk' (Subgroup.center Q)).comp
    (N.comap (QuotientGroup.mk' (Subgroup.center Q))).subtype)).codRestrict N fun x => x.2)

omit [Finite Q] in
theorem zα_eq_one_iff (e : ↥N ≃* Z4C) (x : ↥(N.comap (QuotientGroup.mk' (Subgroup.center Q)))) :
    zα e x = 1 ↔ (x : Q) ∈ Subgroup.center Q := by
  rw [zα, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, Subtype.ext_iff]
  show (QuotientGroup.mk (x : Q) : Q ⧸ Subgroup.center Q) = 1 ↔ _
  exact QuotientGroup.eq_one_iff _

omit [Finite Q] in
theorem zα_surjective (e : ↥N ≃* Z4C) : Function.Surjective (zα e) := by
  intro a
  obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) (e.symm a : Q ⧸ _)
  have hqN : q ∈ N.comap (QuotientGroup.mk' (Subgroup.center Q)) := by
    show QuotientGroup.mk' _ q ∈ N
    rw [hq]
    exact (e.symm a).2
  refine ⟨⟨q, hqN⟩, ?_⟩
  apply e.symm.injective
  rw [zα, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  exact Subtype.ext hq

omit [Finite Q] in
theorem zα_eq_iff (e : ↥N ≃* Z4C) (x y : ↥(N.comap (QuotientGroup.mk' (Subgroup.center Q)))) :
    zα e x = zα e y ↔ ((x : Q)⁻¹ * y) ∈ Subgroup.center Q := by
  rw [show ((x : Q))⁻¹ * y = ((x⁻¹ * y : ↥(N.comap (QuotientGroup.mk' (Subgroup.center Q)))) : Q)
    from rfl, ← zα_eq_one_iff e (x⁻¹ * y), map_mul, map_inv, inv_mul_eq_one]

theorem exists_conj_aut (e : ↥N ≃* Z4C) {t : Q}
    (ht : t ∈ Subgroup.normalizer
      ((N.comap (QuotientGroup.mk' (Subgroup.center Q)) : Subgroup Q) : Set Q)) :
    ∃ φ : MulAut Z4C, ∀ x : ↥(N.comap (QuotientGroup.mk' (Subgroup.center Q))),
      φ (zα e x) = zα e ⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.1 ht x).1 x.2⟩ := by
  set O := N.comap (QuotientGroup.mk' (Subgroup.center Q)) with hO
  set g : Q ⧸ Subgroup.center Q := QuotientGroup.mk' _ t with hg
  have hgN : ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro n hn
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) n
    have hq : q ∈ O := hn
    have h1 : t * q * t⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 ht q).1 hq
    have h2 : QuotientGroup.mk' (Subgroup.center Q) (t * q * t⁻¹) ∈ N := h1
    rwa [map_mul, map_mul, map_inv] at h2
  let cN : ↥N →* ↥N :=
    { toFun := fun n => ⟨g * (n : Q ⧸ Subgroup.center Q) * g⁻¹, hgN n n.2⟩
      map_one' := Subtype.ext (by simp only [OneMemClass.coe_one, mul_one, mul_inv_cancel])
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcN : Function.Injective cN := by
    intro a b h
    have h1 : g * (a : Q ⧸ Subgroup.center Q) * g⁻¹ = g * (b : Q ⧸ Subgroup.center Q) * g⁻¹ :=
      congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  refine ⟨e.symm.trans ((MulEquiv.ofBijective cN
    ⟨hcN, Finite.injective_iff_surjective.1 hcN⟩).trans e), fun x => ?_⟩
  show e (cN (e.symm (e _))) = e _
  rw [MulEquiv.symm_apply_apply]
  congr 1

theorem comm_of_z4c (hZ2 : Nat.card (Subgroup.center Q) ≤ 2) (e : ↥N ≃* Z4C) {t : Q}
    (ht : t ∈ Subgroup.normalizer
      ((N.comap (QuotientGroup.mk' (Subgroup.center Q)) : Subgroup Q) : Set Q))
    (ht7 : t ^ 7 ∈ Subgroup.center Q)
    (htN : ∃ x ∈ N.comap (QuotientGroup.mk' (Subgroup.center Q)),
      (t * x * t⁻¹)⁻¹ * x ∉ Subgroup.center Q) :
    ∀ x ∈ N.comap (QuotientGroup.mk' (Subgroup.center Q)),
      ∀ y ∈ N.comap (QuotientGroup.mk' (Subgroup.center Q)), x * y = y * x := by
  classical
  set O := N.comap (QuotientGroup.mk' (Subgroup.center Q)) with hO
  set Z := Subgroup.center Q with hZ
  have hz2 : ∀ z ∈ Z, z ^ 2 = 1 := fun z hz => sq_eq_one_of_card_le_two hZ2 hz
  have hzc : ∀ z ∈ Z, ∀ g : Q, g * z = z * g := fun z hz => Subgroup.mem_center_iff.1 hz
  have hcomm : ∀ x ∈ O, ∀ y ∈ O, ⁅x, y⁆ ∈ Z := by
    intro x hx y hy
    have h1 : zα e ⁅(⟨x, hx⟩ : ↥O), ⟨y, hy⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    exact (zα_eq_one_iff e _).1 h1
  have hsq : ∀ w ∈ O, ∀ y ∈ O, w ^ 2 * y = y * w ^ 2 := by
    intro w hw y hy
    have h1 : ⁅w ^ 2, y⁆ = 1 := by
      rw [sq, commutator_mul_left (hcomm w hw y hy), ← sq, hz2 _ (hcomm w hw y hy)]
    rwa [commutatorElement_eq_one_iff_mul_comm] at h1
  have hE : ∀ x : ↥O, (zα e x) ^ 2 = 1 → ∀ y ∈ O, (x : Q) * y = y * x := by
    intro x hx y hy
    obtain ⟨b, hb⟩ := Z4C.exists_sq_eq _ hx
    obtain ⟨w, rfl⟩ := zα_surjective e b
    have h1 : zα e (w ^ 2) = zα e x := by rw [map_pow, hb]
    have hz := (zα_eq_iff e _ _).1 h1
    set z := ((w ^ 2 : ↥O) : Q)⁻¹ * x with hzdef
    have hx' : (x : Q) = (w : Q) ^ 2 * z := by
      rw [hzdef]
      simp only [SubgroupClass.coe_pow]
      group
    rw [hx']
    calc (w : Q) ^ 2 * z * y = (w : Q) ^ 2 * (z * y) := by rw [mul_assoc]
      _ = (w : Q) ^ 2 * (y * z) := by rw [← hzc z hz y]
      _ = ((w : Q) ^ 2 * y) * z := by rw [mul_assoc]
      _ = (y * (w : Q) ^ 2) * z := by rw [hsq w w.2 y hy]
      _ = y * ((w : Q) ^ 2 * z) := by rw [mul_assoc]
  have hsame : ∀ u u' : ↥O, (zα e u) ^ 2 = (zα e u') ^ 2 →
      ∀ v ∈ O, ⁅v, (u' : Q)⁆ = ⁅v, (u : Q)⁆ := by
    intro u u' huu v hv
    have h1 : (zα e (u⁻¹ * u')) ^ 2 = 1 := by
      rw [map_mul, map_inv, mul_pow, inv_pow, huu, inv_mul_cancel]
    have hc : ⁅v, ((u⁻¹ * u' : ↥O) : Q)⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (hE _ h1 v hv).symm
    have hu' : (u' : Q) = u * ((u⁻¹ * u' : ↥O) : Q) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [hu', commutator_mul_right (hcomm v hv _ (u⁻¹ * u').2), hc, mul_one]
  obtain ⟨φ, hφ⟩ := exists_conj_aut e ht
  have htk : ∀ k : ℕ, t ^ k ∈ Subgroup.normalizer (O : Set Q) := fun k =>
    Subgroup.pow_mem _ ht k
  have hφk : ∀ (k : ℕ) (x : ↥O), (φ ^ k) (zα e x) =
      zα e ⟨t ^ k * x * (t ^ k)⁻¹, (Subgroup.mem_normalizer_iff.1 (htk k) x).1 x.2⟩ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, ih, hφ]
      congr 1
      apply Subtype.ext
      simp only [pow_succ', mul_inv_rev]
      group
  have hφ7 : φ ^ 7 = 1 := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨x, rfl⟩ := zα_surjective e a
    rw [hφk 7, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show t ^ 7 * x * (t ^ 7)⁻¹ = x
    rw [← hzc _ ht7, mul_assoc, mul_inv_cancel, mul_one]
  have hφ1 : φ ≠ 1 := by
    intro h1
    obtain ⟨x, hx, hxt⟩ := htN
    apply hxt
    have h2 := hφ ⟨x, hx⟩
    rw [h1, MulAut.one_apply, eq_comm] at h2
    exact (zα_eq_iff e _ _).1 h2
  have hcen_conj : ∀ (k : ℕ) (v : Q), v ∈ O → (∀ y ∈ O, v * y = y * v) →
      ∀ y ∈ O, (t ^ k * v * (t ^ k)⁻¹) * y = y * (t ^ k * v * (t ^ k)⁻¹) := by
    intro k v hv hvc y hy
    have hy' : (t ^ k)⁻¹ * y * t ^ k ∈ O := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (htk k)) y).1 hy
      simpa using this
    have h1 := hvc _ hy'
    calc t ^ k * v * (t ^ k)⁻¹ * y = t ^ k * (v * ((t ^ k)⁻¹ * y * t ^ k)) * (t ^ k)⁻¹ := by
          group
      _ = t ^ k * (((t ^ k)⁻¹ * y * t ^ k) * v) * (t ^ k)⁻¹ := by rw [h1]
      _ = y * (t ^ k * v * (t ^ k)⁻¹) := by group
  by_contra hne
  push Not at hne
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy⟩ := hne
  have hinv2 : ∀ c : Z4C, c ^ 2 = 1 → c⁻¹ = c := fun c hc => by
    rw [inv_eq_iff_mul_eq_one, ← sq, hc]
  have hsq2 : ∀ c : Z4C, (c ^ 2) ^ 2 = 1 := fun c => by rw [← pow_mul, Z4C.pow_four]
  have step1 : ∀ v : ↥O, (∀ y ∈ O, (v : Q) * y = y * v) → (zα e v) ^ 2 = 1 := by
    intro v hv
    by_contra hs
    apply hxy
    have hall : ∀ u : ↥O, ∀ y ∈ O, (u : Q) * y = y * u := by
      intro u
      by_cases hu : (zα e u) ^ 2 = 1
      · exact hE u hu
      · obtain ⟨k, hk⟩ := Z4C.exists_pow_eq φ hφ7 hφ1 (hsq2 (zα e v)) hs (hsq2 (zα e u)) hu
        rw [map_pow, hφk k v] at hk
        intro y hy
        have h1 := hsame _ u hk y hy
        have h2 : ⁅y, t ^ k * (v : Q) * (t ^ k)⁻¹⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact (hcen_conj k v v.2 hv y hy).symm
        rw [h2, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1.symm
    exact hall ⟨x₀, hx₀⟩ y₀ hy₀
  set a := (zα e ⟨x₀, hx₀⟩) ^ 2 with ha
  set c := (zα e ⟨y₀, hy₀⟩) ^ 2 with hc
  have ha1 : a ≠ 1 := fun h => hxy (hE ⟨x₀, hx₀⟩ h y₀ hy₀)
  have hc1 : c ≠ 1 := fun h => hxy ((hE ⟨y₀, hy₀⟩ h x₀ hx₀).symm)
  have hca : c ≠ a := by
    intro h
    have h1 := hsame ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩ h.symm x₀ hx₀
    rw [commutatorElement_self, commutatorElement_eq_one_iff_mul_comm] at h1
    exact hxy h1
  have hxy₀ : ⁅x₀, y₀⁆ ≠ 1 := by
    rwa [Ne, commutatorElement_eq_one_iff_mul_comm]
  obtain ⟨⟨b, hb⟩, hb1, hba, hbc, hbac⟩ := Z4C.exists_ne_four ⟨a, hsq2 _⟩ ⟨c, hsq2 _⟩
  simp only at hb1 hba hbc hbac
  obtain ⟨b', hb'⟩ := Z4C.exists_sq_eq b hb
  obtain ⟨u, rfl⟩ := zα_surjective e b'
  obtain ⟨y, hyx, hy1, hya, hyc, hyac⟩ : ∃ y : ↥O, (x₀ : Q) * y = y * x₀ ∧
      (zα e y) ^ 2 ≠ 1 ∧ (zα e y) ^ 2 ≠ a ∧ (zα e y) ^ 2 ≠ c ∧ (zα e y) ^ 2 ≠ a * c := by
    by_cases hu : x₀ * (u : Q) = u * x₀
    · exact ⟨u, hu, by rwa [hb'], by rwa [hb'], by rwa [hb'], by rwa [hb']⟩
    · refine ⟨u * (⟨y₀, hy₀⟩ : ↥O)⁻¹, ?_, ?_⟩
      · have hux : ⁅x₀, (u : Q)⁆ ≠ 1 := by rwa [Ne, commutatorElement_eq_one_iff_mul_comm]
        have heq : ⁅x₀, (u : Q)⁆ = ⁅x₀, y₀⁆ := eq_of_ne_one_of_card_le_two hZ2
          (hcomm x₀ hx₀ u u.2) (hcomm x₀ hx₀ y₀ hy₀) hux hxy₀
        have hinv : ⁅x₀, y₀⁻¹⁆ = ⁅x₀, y₀⁆⁻¹ := by
          have h1 := commutator_mul_right (x := x₀) (u := y₀) (hcomm x₀ hx₀ _ (O.inv_mem hy₀))
          rw [mul_inv_cancel, commutatorElement_one_right] at h1
          exact eq_inv_of_mul_eq_one_right h1.symm
        have h1 : ⁅x₀, ((u * (⟨y₀, hy₀⟩ : ↥O)⁻¹ : ↥O) : Q)⁆ = 1 := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [commutator_mul_right (hcomm x₀ hx₀ _ (O.inv_mem hy₀)), hinv, heq, mul_inv_cancel]
        rwa [commutatorElement_eq_one_iff_mul_comm] at h1
      · rw [map_mul, map_inv, mul_pow, inv_pow, hb', ← hc, hinv2 c (hsq2 _)]
        refine ⟨fun h => hbc ?_, fun h => hbac ?_, fun h => hb1 ?_, fun h => hba ?_⟩
        · calc b = b * c * c := by rw [mul_assoc, ← sq, hsq2, mul_one]
            _ = c := by rw [h, one_mul]
        · calc b = b * c * c := by rw [mul_assoc, ← sq, hsq2, mul_one]
            _ = a * c := by rw [h]
        · calc b = b * c * c := by rw [mul_assoc, ← sq, hsq2, mul_one]
            _ = 1 := by rw [h, ← sq, hsq2]
        · calc b = b * c * c := by rw [mul_assoc, ← sq, hsq2, mul_one]
            _ = a := by rw [h, mul_assoc, ← sq, hsq2, mul_one]
  obtain ⟨w, hw1, hwx, hwy, hwz⟩ : ∃ w : ↥O, (zα e w) ^ 2 ≠ 1 ∧ (w : Q) * x₀ = x₀ * w ∧
      (w : Q) * y = y * w ∧ (w : Q) * y₀ = y₀ * w := by
    by_cases hyz : (y : Q) * y₀ = y₀ * y
    · exact ⟨y, hy1, hyx.symm, rfl, hyz⟩
    · refine ⟨⟨x₀, hx₀⟩ * y, ?_, ?_, ?_, ?_⟩
      · rw [map_mul, mul_pow, ← ha]
        intro h
        apply hya
        calc (zα e y) ^ 2 = a * (a * (zα e y) ^ 2) := by
              rw [← mul_assoc, ← sq, hsq2, one_mul]
          _ = a := by rw [h, mul_one]
      · simp only [Subgroup.coe_mul]
        calc x₀ * (y : Q) * x₀ = x₀ * ((y : Q) * x₀) := by rw [mul_assoc]
          _ = x₀ * (x₀ * y) := by rw [← hyx]
      · simp only [Subgroup.coe_mul]
        calc x₀ * (y : Q) * y = ((y : Q) * x₀) * y := by rw [hyx]
          _ = y * (x₀ * y) := by rw [mul_assoc]
      · simp only [Subgroup.coe_mul]
        have hyz' : ⁅(y : Q), y₀⁆ ≠ 1 := by rwa [Ne, commutatorElement_eq_one_iff_mul_comm]
        have heq : ⁅x₀, y₀⁆ = ⁅(y : Q), y₀⁆ := eq_of_ne_one_of_card_le_two hZ2
          (hcomm x₀ hx₀ y₀ hy₀) (hcomm y y.2 y₀ hy₀) hxy₀ hyz'
        have h1 : ⁅x₀ * (y : Q), y₀⁆ = 1 := by
          rw [commutator_mul_left (hcomm y y.2 y₀ hy₀), heq, ← sq, hz2 _ (hcomm y y.2 y₀ hy₀)]
        rwa [commutatorElement_eq_one_iff_mul_comm] at h1
  apply hw1
  refine step1 w fun u' hu' => ?_
  obtain ⟨i, j, k, hijk⟩ := Z4C.span_three (hsq2 (zα e ⟨x₀, hx₀⟩)) (hsq2 (zα e y))
    (hsq2 (zα e ⟨y₀, hy₀⟩)) (hsq2 (zα e ⟨u', hu'⟩)) ha1 hy1 hya hc1 hca (Ne.symm hyc)
    (fun h => hyac (by
      calc (zα e y) ^ 2 = a * (a * (zα e y) ^ 2) := by rw [← mul_assoc, ← sq, hsq2, one_mul]
        _ = a * c := by rw [← h]))
  set p : ↥O := (bif i then ⟨x₀, hx₀⟩ else 1) * (bif j then y else 1) *
    (bif k then ⟨y₀, hy₀⟩ else 1) with hp
  have hps : (zα e p) ^ 2 = (zα e ⟨u', hu'⟩) ^ 2 := by
    rw [hijk, hp]
    cases i <;> cases j <;> cases k <;>
      simp only [Bool.cond_true, Bool.cond_false, map_mul, map_one, mul_pow, one_pow, mul_one,
        one_mul]
  have hwp : (w : Q) * p = p * w := by
    have hx : Commute (w : Q) ((bif i then (⟨x₀, hx₀⟩ : ↥O) else 1 : ↥O) : Q) := by
      cases i
      · exact Commute.one_right _
      · exact hwx
    have hy' : Commute (w : Q) ((bif j then y else 1 : ↥O) : Q) := by
      cases j
      · exact Commute.one_right _
      · exact hwy
    have hz' : Commute (w : Q) ((bif k then (⟨y₀, hy₀⟩ : ↥O) else 1 : ↥O) : Q) := by
      cases k
      · exact Commute.one_right _
      · exact hwz
    have hc' : Commute (w : Q) (p : Q) := by
      rw [hp, Subgroup.coe_mul, Subgroup.coe_mul]
      exact (hx.mul_right hy').mul_right hz'
    exact hc'.eq
  have h1 := hsame p ⟨u', hu'⟩ hps w w.2
  rw [show ⁅(w : Q), (p : Q)⁆ = 1 by rwa [commutatorElement_eq_one_iff_mul_comm],
    commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

omit [Finite Q] in
theorem inf_center_eq_bot_of_complement {M₀ V E' : Subgroup Q} (hVM : ⁅V, M₀⁆ = V)
    (hE'n : M₀ ≤ Subgroup.normalizer (E' : Set Q)) (hE'Z : E' ⊓ Subgroup.center Q = ⊥)
    (hV : V ≤ E' ⊔ Subgroup.center Q) : V ⊓ Subgroup.center Q = ⊥ := by
  have hVE : V ≤ E' := by
    rw [← hVM, Subgroup.commutator_le]
    intro v hv m hm
    have hv' : v ∈ ((E' ⊔ Subgroup.center Q : Subgroup Q) : Set Q) := hV hv
    rw [Subgroup.mul_normal] at hv'
    obtain ⟨x, hx, z, hz, rfl⟩ := hv'
    have hzc := Subgroup.mem_center_iff.mp hz
    have h1 : ⁅x * z, m⁆ = x * (m * x⁻¹ * m⁻¹) := by
      rw [commutatorElement_def, mul_inv_rev, show x * z * m * (z⁻¹ * x⁻¹) * m⁻¹ =
        x * (z * m * z⁻¹) * x⁻¹ * m⁻¹ by group, ← hzc m, mul_inv_cancel_right]
      group
    rw [h1]
    exact E'.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hE'n hm) _).mp (E'.inv_mem hx))
  rw [eq_bot_iff, ← hE'Z]
  exact inf_le_inf_right _ hVE

theorem inf_center_eq_bot_of_z4c (hZ2 : Nat.card (Subgroup.center Q) ≤ 2) (e : ↥N ≃* Z4C)
    {M₀ : Subgroup Q} (hM₀ : M₀ ≤ Subgroup.normalizer
      ((N.comap (QuotientGroup.mk' (Subgroup.center Q)) : Subgroup Q) : Set Q))
    {t : Q} (ht : t ∈ M₀) (ht7 : t ^ 7 ∈ Subgroup.center Q)
    (htN : ∃ x ∈ N.comap (QuotientGroup.mk' (Subgroup.center Q)),
      (t * x * t⁻¹)⁻¹ * x ∉ Subgroup.center Q)
    {V : Subgroup Q} (hVO : V ≤ N.comap (QuotientGroup.mk' (Subgroup.center Q)))
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hVM : ⁅V, M₀⁆ = V) : V ⊓ Subgroup.center Q = ⊥ := by
  classical
  set O := N.comap (QuotientGroup.mk' (Subgroup.center Q)) with hO
  set Z := Subgroup.center Q with hZ
  have hz2 : ∀ z ∈ Z, z ^ 2 = 1 := fun z hz => sq_eq_one_of_card_le_two hZ2 hz
  have hzc : ∀ z ∈ Z, ∀ g : Q, g * z = z * g := fun z hz => Subgroup.mem_center_iff.1 hz
  have hab := comm_of_z4c hZ2 e (hM₀ ht) ht7 htN
  have hZO : Z ≤ O := fun z hz => by
    show QuotientGroup.mk' Z z ∈ N
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz]
    exact N.one_mem
  have hsq2 : ∀ c : Z4C, (c ^ 2) ^ 2 = 1 := fun c => by rw [← pow_mul, Z4C.pow_four]
  have hpow_sq : ∀ x y : Q, x ∈ O → y ∈ O → (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
    intro x y hx hy
    rw [sq, sq, sq, mul_assoc, ← mul_assoc y x y, ← hab x hx y hy]
    group
  obtain ⟨φ, hφ⟩ := exists_conj_aut e (hM₀ ht)
  have htk : ∀ k : ℕ, t ^ k ∈ Subgroup.normalizer (O : Set Q) := fun k =>
    Subgroup.pow_mem _ (hM₀ ht) k
  have hφk : ∀ (k : ℕ) (x : ↥O), (φ ^ k) (zα e x) =
      zα e ⟨t ^ k * x * (t ^ k)⁻¹, (Subgroup.mem_normalizer_iff.1 (htk k) x).1 x.2⟩ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, ih, hφ]
      congr 1
      apply Subtype.ext
      simp only [pow_succ', mul_inv_rev]
      group
  have hφ7 : φ ^ 7 = 1 := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨x, rfl⟩ := zα_surjective e a
    rw [hφk 7, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show t ^ 7 * x * (t ^ 7)⁻¹ = x
    rw [← hzc _ ht7, mul_assoc, mul_inv_cancel, mul_one]
  have hφ1 : φ ≠ 1 := by
    intro h1
    obtain ⟨x, hx, hxt⟩ := htN
    apply hxt
    have h2 := hφ ⟨x, hx⟩
    rw [h1, MulAut.one_apply, eq_comm] at h2
    exact (zα_eq_iff e _ _).1 h2
  have hE2 : ∀ x : ↥O, (zα e x) ^ 2 = 1 → (x : Q) ^ 2 = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x₁, hx₁, hx₁2⟩ := hcon
    have hx₁1 : zα e x₁ ≠ 1 := fun h => hx₁2 (hz2 _ ((zα_eq_one_iff e x₁).1 h))
    have hx₁Z : (x₁ : Q) ^ 2 ∈ Z := by
      have : zα e (x₁ ^ 2) = 1 := by rw [map_pow, hx₁]
      exact (zα_eq_one_iff e _).1 this
    have hall : ∀ x : ↥O, (zα e x) ^ 2 = 1 → zα e x ≠ 1 → (x : Q) ^ 2 = (x₁ : Q) ^ 2 := by
      intro x hx hx1
      obtain ⟨k, hk⟩ := Z4C.exists_pow_eq φ hφ7 hφ1 hx₁ hx₁1 hx hx1
      rw [hφk k x₁] at hk
      have hz := (zα_eq_iff e _ _).1 hk
      set y : ↥O := ⟨t ^ k * x₁ * (t ^ k)⁻¹, (Subgroup.mem_normalizer_iff.1 (htk k) x₁).1 x₁.2⟩
      have hxy : (x : Q) = y * ((y : Q)⁻¹ * x) := by group
      rw [hxy, hpow_sq _ _ y.2 (hZO hz), hz2 _ hz, mul_one]
      show (t ^ k * x₁ * (t ^ k)⁻¹) ^ 2 = (x₁ : Q) ^ 2
      rw [conj_pow, hzc _ hx₁Z (t ^ k), mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨⟨b, hb⟩, hb1, hba, -, hbac⟩ := Z4C.exists_ne_four ⟨zα e x₁, hx₁⟩ ⟨1, one_pow 2⟩
    simp only [mul_one] at hb1 hba hbac
    obtain ⟨x', rfl⟩ := zα_surjective e b
    have hx'2 := hall x' hb hb1
    have hprod : (zα e (x₁ * x')) ^ 2 = 1 := by
      rw [map_mul, mul_pow, hx₁, hb, one_mul]
    have hprod1 : zα e (x₁ * x') ≠ 1 := by
      rw [map_mul]
      intro h
      apply hba
      rw [eq_inv_of_mul_eq_one_right h, inv_eq_iff_mul_eq_one, ← sq, hx₁]
    have h3 := hall (x₁ * x') hprod hprod1
    rw [Subgroup.coe_mul, hpow_sq _ _ x₁.2 x'.2, hx'2] at h3
    apply hx₁2
    have h4 : (x₁ : Q) ^ 2 * (x₁ : Q) ^ 2 = 1 := by rw [← sq, hz2 _ hx₁Z]
    rw [h4] at h3
    exact h3.symm
  let E' : Subgroup Q :=
    { carrier := {x | ∃ y ∈ O, y ^ 2 = x}
      mul_mem' := by
        rintro _ _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
        exact ⟨y₁ * y₂, O.mul_mem hy₁ hy₂, hpow_sq _ _ hy₁ hy₂⟩
      one_mem' := ⟨1, O.one_mem, one_pow 2⟩
      inv_mem' := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨y⁻¹, O.inv_mem hy, inv_pow y 2⟩ }
  refine inf_center_eq_bot_of_complement (E' := E') hVM ?_ ?_ ?_
  · intro m hm
    have hmO := hM₀ hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨m * y * m⁻¹, (Subgroup.mem_normalizer_iff.1 hmO y).1 hy, by rw [conj_pow]⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨m⁻¹ * y * m, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hmO) y).1 hy
        simpa using this
      · rw [show m⁻¹ * y * m = m⁻¹ * y * m⁻¹⁻¹ by rw [inv_inv], conj_pow, hyx]
        group
  · rw [eq_bot_iff]
    rintro _ ⟨⟨y, hy, rfl⟩, hyZ⟩
    have h1 : zα e (⟨y, hy⟩ ^ 2) = 1 := (zα_eq_one_iff e _).2 hyZ
    rw [map_pow] at h1
    exact hE2 ⟨y, hy⟩ h1
  · intro v hv
    have hvO := hVO hv
    have h1 : (zα e ⟨v, hvO⟩) ^ 2 = 1 := by
      rw [← map_pow]
      exact (zα_eq_one_iff e _).2 (by
        show v ^ 2 ∈ Z
        rw [hV2 v hv]
        exact Z.one_mem)
    obtain ⟨b, hb⟩ := Z4C.exists_sq_eq _ h1
    obtain ⟨w, rfl⟩ := zα_surjective e b
    have h2 : zα e (w ^ 2) = zα e ⟨v, hvO⟩ := by rw [map_pow, hb]
    have hz := (zα_eq_iff e _ _).1 h2
    have hv' : v = ((w : Q) ^ 2) * (((w ^ 2 : ↥O) : Q)⁻¹ * v) := by
      simp only [SubgroupClass.coe_pow]
      group
    rw [hv']
    exact Subgroup.mul_mem_sup ⟨w, w.2, rfl⟩ hz

end Core

end CFSG.Quasithin.C48Cover

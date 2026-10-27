module

public import CFSG.Timmesfeld.Basic
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Timmesfeld.CorB

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X]

@[expose] def conjCent (t : X) : Set X := {τ | τ * t = t * τ ∧ IsConj t τ}

@[expose] def weakClosure (t : X) : Subgroup X := closure (conjCent t)

@[expose] def cls (t : X) : Set X := {x | IsConj t x}

structure Setup (t : X) : Prop where
  orderOf_eq : orderOf t = 2
  isPGroup : IsPGroup 2 (weakClosure t)
  class_two : ⁅⁅weakClosure t, weakClosure t⁆, weakClosure t⁆ = ⊥
  fusion : ∀ τ : X, τ * t = t * τ → IsConj t τ → τ ≠ t → IsConj t (t * τ)

@[expose] def NoOddCent {G : Type*} [Group G] (D : Set G) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, Commute x y → Commute x z → Odd (orderOf (y * z)) → y = z

theorem orderOf_conj (g x : X) : orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g (show g * x = g * x * g⁻¹ * g by group)).symm

theorem mem_cls_self (t : X) : t ∈ cls t := IsConj.refl t

theorem conj_mem_cls {t x : X} (g : X) (hx : x ∈ cls t) : g * x * g⁻¹ ∈ cls t :=
  IsConj.trans hx (isConj_iff.mpr ⟨g, rfl⟩)

theorem exists_conj_of_mem_cls {t x : X} (hx : x ∈ cls t) : ∃ g : X, g * t * g⁻¹ = x :=
  isConj_iff.mp hx

theorem normalClosure_eq (t : X) : normalClosure ({t} : Set X) = closure (cls t) := by
  rw [normalClosure]
  congr 1
  ext x
  simp only [Group.mem_conjugatesOfSet_iff, Set.mem_singleton_iff, exists_eq_left]
  rfl

theorem cls_subset (t : X) : cls t ⊆ normalClosure ({t} : Set X) := by
  rw [normalClosure_eq]
  exact subset_closure

theorem conj_mem_conjCent {t x y g : X} (hg : g * t * g⁻¹ = x) (hy : y ∈ cls t)
    (hxy : Commute x y) : g⁻¹ * y * g ∈ conjCent t := by
  refine ⟨?_, by have := conj_mem_cls g⁻¹ hy; rwa [inv_inv] at this⟩
  subst hg
  have h := hxy.eq
  calc g⁻¹ * y * g * t = g⁻¹ * (y * (g * t * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * t * g⁻¹) * y) * g := by rw [h]
    _ = t * (g⁻¹ * y * g) := by group

theorem commute_conj {x y : X} (g : X) (h : Commute x y) :
    Commute (g * x * g⁻¹) (g * y * g⁻¹) := by
  change _ * _ = _ * _
  calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    _ = g * (y * x) * g⁻¹ := by rw [h.eq]
    _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group

namespace Setup

variable {t : X} (h : Setup t)
include h

theorem mul_self {x : X} (hx : x ∈ cls t) : x * x = 1 := by
  obtain ⟨g, rfl⟩ := exists_conj_of_mem_cls hx
  have ht : t * t = 1 := by rw [← pow_two, ← h.orderOf_eq, pow_orderOf_eq_one]
  calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
    _ = 1 := by rw [ht, mul_one, mul_inv_cancel]

theorem orderOf_mem {x : X} (hx : x ∈ cls t) : orderOf x = 2 := by
  obtain ⟨g, rfl⟩ := exists_conj_of_mem_cls hx
  rw [orderOf_conj, h.orderOf_eq]

theorem mul_mem {d e : X} (hd : d ∈ cls t) (he : e ∈ cls t) (hde : Commute d e) (hne : d ≠ e) :
    d * e ∈ cls t := by
  obtain ⟨g, rfl⟩ := exists_conj_of_mem_cls hd
  have hτ := conj_mem_conjCent rfl he hde
  have hne' : g⁻¹ * e * g ≠ t := by
    intro heq
    apply hne
    rw [← heq]
    group
  have key := h.fusion _ hτ.1 hτ.2 hne'
  have := conj_mem_cls g key
  rw [show g * t * g⁻¹ * e = g * (t * (g⁻¹ * e * g)) * g⁻¹ by group]
  exact this

omit h in
theorem exists_mem_weakClosure {x y z : X} (hx : x ∈ cls t) (hy : y ∈ cls t) (hz : z ∈ cls t)
    (hxy : Commute x y) (hxz : Commute x z) :
    ∃ g : X, g⁻¹ * y * g ∈ weakClosure t ∧ g⁻¹ * z * g ∈ weakClosure t := by
  obtain ⟨g, hg⟩ := exists_conj_of_mem_cls hx
  exact ⟨g, subset_closure (conj_mem_conjCent hg hy hxy),
    subset_closure (conj_mem_conjCent hg hz hxz)⟩

theorem exists_orderOf_eq_two_pow {x y z : X} (hx : x ∈ cls t) (hy : y ∈ cls t)
    (hz : z ∈ cls t) (hxy : Commute x y) (hxz : Commute x z) :
    ∃ k : ℕ, orderOf (y * z) = 2 ^ k := by
  obtain ⟨g, hy', hz'⟩ := exists_mem_weakClosure hx hy hz hxy hxz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h.isPGroup ⟨_, (weakClosure t).mul_mem hy' hz'⟩
  refine ⟨k, ?_⟩
  rw [Subgroup.orderOf_mk, show g⁻¹ * y * g * (g⁻¹ * z * g) = g⁻¹ * (y * z) * g⁻¹⁻¹ by group,
    orderOf_conj] at hk
  exact hk

theorem eq_of_odd_orderOf_mul {x y z : X} (hx : x ∈ cls t) (hy : y ∈ cls t) (hz : z ∈ cls t)
    (hxy : Commute x y) (hxz : Commute x z) (hodd : Odd (orderOf (y * z))) : y = z := by
  obtain ⟨k, hk⟩ := h.exists_orderOf_eq_two_pow hx hy hz hxy hxz
  have hk0 : k = 0 := by
    by_contra hk0
    rw [hk] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hk0).mpr even_two)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  rw [eq_inv_of_mul_eq_one_left hk, inv_eq_of_mul_eq_one_right (h.mul_self hz)]

theorem noOddCent : NoOddCent (cls t) :=
  fun _ hx _ hy _ hz hxy hxz hodd => h.eq_of_odd_orderOf_mul hx hy hz hxy hxz hodd

theorem pow_four_eq_one {x y z : X} (hx : x ∈ cls t) (hy : y ∈ cls t) (hz : z ∈ cls t)
    (hxy : Commute x y) (hxz : Commute x z) : (y * z) ^ 4 = 1 := by
  obtain ⟨g, hy', hz'⟩ := exists_mem_weakClosure hx hy hz hxy hxz
  have hc : ⁅⁅g⁻¹ * y * g, g⁻¹ * z * g⁆, g⁻¹ * y * g⁆ = 1 := by
    have hmem := commutator_mem_commutator (commutator_mem_commutator hy' hz') hy'
    rw [h.class_two, mem_bot] at hmem
    exact hmem
  have hc' : ⁅⁅y, z⁆, y⁆ = 1 := by
    have e : ⁅⁅g⁻¹ * y * g, g⁻¹ * z * g⁆, g⁻¹ * y * g⁆ = g⁻¹ * ⁅⁅y, z⁆, y⁆ * g := by
      simp only [commutatorElement_def]
      group
    rw [e] at hc
    calc ⁅⁅y, z⁆, y⁆ = g * (g⁻¹ * ⁅⁅y, z⁆, y⁆ * g) * g⁻¹ := by group
      _ = 1 := by rw [hc, mul_one, mul_inv_cancel]
  have hy2 := h.mul_self hy
  have hz2 := h.mul_self hz
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have h1 : ⁅y, z⁆ = (y * z) ^ 2 := by
    rw [commutatorElement_def, hyi, hzi, pow_two, mul_assoc]
  have h2 : y * (y * z) ^ (-2 : ℤ) = (y * z) ^ (2 : ℤ) * y := by
    rw [mul_zpow_mul_eq_zpow_neg_mul hy2 hz2, neg_neg]
  rw [h1, commutatorElement_def, hyi] at hc'
  have h3 : ((y * z) ^ 2)⁻¹ = (y * z) ^ (-2 : ℤ) := by
    rw [zpow_neg, zpow_ofNat]
  rw [h3, show (y * z) ^ 2 * y * (y * z) ^ (-2 : ℤ) * y =
      (y * z) ^ 2 * (y * (y * z) ^ (-2 : ℤ)) * y by group, h2, zpow_ofNat] at hc'
  calc (y * z) ^ 4 = (y * z) ^ 2 * ((y * z) ^ 2 * y) * y := by
        rw [mul_assoc, mul_assoc, hy2, mul_one, ← pow_add]
    _ = 1 := hc'

theorem orderOf_mul_dvd_four {x y z : X} (hx : x ∈ cls t) (hy : y ∈ cls t) (hz : z ∈ cls t)
    (hxy : Commute x y) (hxz : Commute x z) : orderOf (y * z) ∣ 4 :=
  orderOf_dvd_of_pow_eq_one (h.pow_four_eq_one hx hy hz hxy hxz)

omit h in
theorem mul_zpow_mul_eq_zpow_neg_mul' {d e : X} (hd : d * d = 1) (he : e * e = 1) (i : ℤ) :
    e * (d * e) ^ i = (d * e) ^ (-i) * e := by
  have hinv : (e * d) = (d * e)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hd, inv_eq_of_mul_eq_one_right he]
  have key := mul_zpow_mul_eq_zpow_neg_mul he hd (-i)
  rw [hinv, inv_zpow', inv_zpow', neg_neg] at key
  exact key

theorem pow_mem_of_orderOf_eq {d e : X} (hd : d ∈ cls t) (he : e ∈ cls t) {m : ℕ}
    (hm : orderOf (d * e) = 2 * m) (hm0 : m ≠ 0) :
    (d * e) ^ m ∈ cls t ∧ Commute d ((d * e) ^ m) ∧ Commute e ((d * e) ^ m) := by
  set r := d * e with hr
  have hd2 := h.mul_self hd
  have he2 := h.mul_self he
  have hz1 : r ^ m ≠ 1 := pow_ne_one_of_lt_orderOf hm0 (by omega)
  have hzz : r ^ m * r ^ m = 1 := by rw [← pow_add, ← two_mul, ← hm, pow_orderOf_eq_one]
  have hzi : (r ^ m)⁻¹ = r ^ m := inv_eq_of_mul_eq_one_right hzz
  have hdz : Commute d (r ^ m) := by
    have key := mul_zpow_mul_eq_zpow_neg_mul hd2 he2 (m : ℤ)
    rw [zpow_neg, zpow_natCast, hzi] at key
    exact key
  have hez : Commute e (r ^ m) := by
    have key := mul_zpow_mul_eq_zpow_neg_mul' hd2 he2 (m : ℤ)
    rw [zpow_neg, zpow_natCast, hzi] at key
    exact key
  have hdzD : d * r ^ m ∈ cls t := by
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' m
    · have key := mul_zpow_mul_eq_zpow_neg_mul hd2 he2 (k : ℤ)
      have e1 : d * r ^ m = r ^ (-(k : ℤ)) * d * (r ^ (-(k : ℤ)))⁻¹ := by
        rw [← key, hk, two_mul, pow_add, zpow_neg, inv_inv, zpow_natCast, mul_assoc]
      rw [e1]
      exact conj_mem_cls _ hd
    · have key := mul_zpow_mul_eq_zpow_neg_mul' hd2 he2 (k : ℤ)
      have e0 : d * r = e := by rw [hr, ← mul_assoc, hd2, one_mul]
      have e1 : d * r ^ m = r ^ (-(k : ℤ)) * e * (r ^ (-(k : ℤ)))⁻¹ := by
        rw [← key, hk, pow_succ', ← mul_assoc, e0, two_mul, pow_add, zpow_neg, inv_inv,
          zpow_natCast, mul_assoc]
      rw [e1]
      exact conj_mem_cls _ he
  have hne : d ≠ d * r ^ m := fun heq => hz1 (by
    have := congrArg (d⁻¹ * ·) heq
    simpa using this.symm)
  have hmem := h.mul_mem hd hdzD ((Commute.refl d).mul_right hdz) hne
  rw [← mul_assoc, hd2, one_mul] at hmem
  exact ⟨hmem, hdz, hez⟩

theorem isRootInvolutionSet [Finite X] : IsRootInvolutionSet (cls t) := by
  refine ⟨fun d hd => h.orderOf_mem hd, fun d hd e he => ?_, fun d hd e he h4 => ?_⟩
  · rcases Nat.even_or_odd (orderOf (d * e)) with ⟨m, hm⟩ | hodd
    · have hm0 : m ≠ 0 := by
        rintro rfl
        have := orderOf_pos (d * e)
        omega
      obtain ⟨hz, hdz, hez⟩ := h.pow_mem_of_orderOf_eq hd he (by omega : _ = 2 * m) hm0
      have hdvd := h.orderOf_mul_dvd_four hz hd he hdz.symm hez.symm
      have hle : orderOf (d * e) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases hn : orderOf (d * e) <;> omega
    · exact Or.inr (Or.inr hodd)
  · exact (h.pow_mem_of_orderOf_eq hd he (by omega : _ = 2 * 2) two_ne_zero).1

end Setup

theorem exists_opposite_of_cls {t : X}
    (hopp : ∃ d ∈ cls t, ∃ e ∈ cls t, ¬ Commute d e ∧ Odd (orderOf (d * e))) :
    ∀ x ∈ cls t, ∃ b ∈ cls t, ¬ Commute x b ∧ Odd (orderOf (x * b)) := by
  obtain ⟨d, hd, e, he, hde, hodd⟩ := hopp
  intro x hx
  obtain ⟨g, rfl⟩ := exists_conj_of_mem_cls hd
  obtain ⟨k, rfl⟩ := exists_conj_of_mem_cls hx
  set c := k * g⁻¹
  have hx' : k * t * k⁻¹ = c * (g * t * g⁻¹) * c⁻¹ := by simp only [c]; group
  refine ⟨c * e * c⁻¹, conj_mem_cls c he, fun hc => hde ?_, ?_⟩
  · rw [hx'] at hc
    have := commute_conj c⁻¹ hc
    simpa [mul_assoc] using this
  · rw [hx', show c * (g * t * g⁻¹) * c⁻¹ * (c * e * c⁻¹) = c * (g * t * g⁻¹ * e) * c⁻¹ by group,
      orderOf_conj]
    exact hodd

theorem forall_commute_of_mem_center {t : X} {u : ↥(normalClosure ({t} : Set X))}
    (hu : u ∈ center ↥(normalClosure ({t} : Set X))) (hut : (u : X) ∈ cls t) :
    ∀ d ∈ cls t, ∀ e ∈ cls t, Commute d e := by
  have hN : (normalClosure ({t} : Set X)).Normal := normalClosure_normal
  have key : ∀ g : X, ∀ v ∈ normalClosure ({t} : Set X), Commute (g * u * g⁻¹) v := by
    intro g v hv
    have hv' : g⁻¹ * v * g⁻¹⁻¹ ∈ normalClosure ({t} : Set X) := hN.conj_mem v hv g⁻¹
    have hc : (u : X) * (g⁻¹ * v * g⁻¹⁻¹) = (g⁻¹ * v * g⁻¹⁻¹) * u := by
      have := mem_center_iff.mp hu ⟨_, hv'⟩
      exact (congrArg Subtype.val this).symm
    have := commute_conj g (show Commute (u : X) (g⁻¹ * v * g⁻¹⁻¹) from hc)
    simpa [mul_assoc] using this
  intro d hd e he
  obtain ⟨k, rfl⟩ := exists_conj_of_mem_cls hd
  obtain ⟨g, hg⟩ := exists_conj_of_mem_cls hut
  have hk : k * t * k⁻¹ = (k * g⁻¹) * u * (k * g⁻¹)⁻¹ := by rw [← hg]; group
  rw [hk]
  exact key _ e (cls_subset t he)

theorem Setup.forall_mul_comm_of_commute {t : X} (h : Setup t)
    (hc : ∀ d ∈ cls t, ∀ e ∈ cls t, Commute d e) :
    ∀ x ∈ normalClosure ({t} : Set X), ∀ y ∈ normalClosure ({t} : Set X),
      x * y = y * x ∧ x * x = 1 := by
  rw [normalClosure_eq]
  have h1 : ∀ x ∈ closure (cls t), ∀ d ∈ cls t, Commute x d := by
    intro x hx
    induction hx using closure_induction with
    | mem x hx => exact fun d hd => hc x hx d hd
    | one => exact fun d _ => Commute.one_left d
    | mul x y _ _ hx hy => exact fun d hd => (hx d hd).mul_left (hy d hd)
    | inv x _ hx => exact fun d hd => (hx d hd).inv_left
  have h2 : ∀ x ∈ closure (cls t), ∀ y ∈ closure (cls t), Commute x y := by
    intro x hx y hy
    induction hy using closure_induction with
    | mem y hy => exact h1 x hx y hy
    | one => exact Commute.one_right x
    | mul y z _ _ hy hz => exact hy.mul_right hz
    | inv y _ hy => exact hy.inv_right
  intro x hx y hy
  refine ⟨(h2 x hx y hy).eq, ?_⟩
  induction hx using closure_induction with
  | mem x hx => exact h.mul_self hx
  | one => exact mul_one 1
  | mul x y hx hy hx' hy' =>
    calc x * y * (x * y) = x * x * (y * y) := by
          rw [mul_assoc, ← mul_assoc y x y, ← (h2 x hx y hy).eq, mul_assoc, mul_assoc]
      _ = 1 := by rw [hx', hy', mul_one]
  | inv x _ hx' => rw [← mul_inv_rev, hx', inv_one]

@[expose] def clsIn (t : X) : Set ↥(normalClosure ({t} : Set X)) := {u | IsConj t (u : X)}

theorem mem_clsIn {t : X} {u : ↥(normalClosure ({t} : Set X))} : u ∈ clsIn t ↔ (u : X) ∈ cls t :=
  Iff.rfl

theorem commute_coe_iff {H : Subgroup X} {u v : ↥H} : Commute (u : X) (v : X) ↔ Commute u v := by
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

theorem closure_clsIn (t : X) : closure (clsIn t) = ⊤ := by
  apply map_injective (normalClosure ({t} : Set X)).subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype]
  have himg : (normalClosure ({t} : Set X)).subtype '' clsIn t = cls t := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hx
      exact ⟨⟨x, cls_subset t hx⟩, hx, rfl⟩
  rw [himg, normalClosure_eq]

theorem conj_mem_clsIn {t : X} (g u : ↥(normalClosure ({t} : Set X))) (hu : u ∈ clsIn t) :
    g * u * g⁻¹ ∈ clsIn t := by
  rw [mem_clsIn]
  push_cast
  exact conj_mem_cls _ hu

namespace Setup

variable {t : X} (h : Setup t)
include h

theorem mul_mem_clsIn {d e : ↥(normalClosure ({t} : Set X))} (hd : d ∈ clsIn t)
    (he : e ∈ clsIn t) (hde : Commute d e) (hne : d ≠ e) : d * e ∈ clsIn t := by
  rw [mem_clsIn]
  push_cast
  exact h.mul_mem hd he (commute_coe_iff.mpr hde) fun heq => hne (Subtype.ext heq)

theorem isRootInvolutionSet_clsIn [Finite X] : IsRootInvolutionSet (clsIn t) := by
  obtain ⟨h1, h2, h3⟩ := h.isRootInvolutionSet
  refine ⟨fun d hd => ?_, fun d hd e he => ?_, fun d hd e he h4 => ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact h1 _ hd
  · rw [← Subgroup.orderOf_coe]
    exact h2 _ hd _ he
  · rw [← Subgroup.orderOf_coe] at h4
    rw [mem_clsIn]
    push_cast
    exact h3 _ hd _ he h4

theorem exists_orderOf_eq_two_pow_clsIn {x y z : ↥(normalClosure ({t} : Set X))}
    (hx : x ∈ clsIn t) (hy : y ∈ clsIn t) (hz : z ∈ clsIn t) (hxy : Commute x y)
    (hxz : Commute x z) : ∃ k : ℕ, orderOf (y * z) = 2 ^ k := by
  rw [← Subgroup.orderOf_coe]
  exact h.exists_orderOf_eq_two_pow hx hy hz (commute_coe_iff.mpr hxy) (commute_coe_iff.mpr hxz)

end Setup

end CFSG.Timmesfeld.CorB

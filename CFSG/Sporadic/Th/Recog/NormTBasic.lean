module

public import CFSG.Monster.B.Recog.GenericIndexTwo
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Amalgam
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.OneClass
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Sporadic.Th.Recog

open Subgroup

variable {A : Type*} [Group A]

theorem eq_one_or_eq_or_eq_inv_of_mem_zpowers {t x : A} (ht : orderOf t = 3)
    (hx : x ∈ zpowers t) : x = 1 ∨ x = t ∨ x = t⁻¹ := by
  classical
  have hfin : IsOfFinOrder t := orderOf_pos_iff.mp (by rw [ht]; norm_num)
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp (hfin.mem_zpowers_iff_mem_range_orderOf.mp hx)
  rw [ht, Finset.mem_range] at hn
  interval_cases n
  · exact Or.inl (pow_zero t)
  · exact Or.inr (Or.inl (pow_one t))
  · refine Or.inr (Or.inr ?_)
    have h3 : t ^ 3 = 1 := ht ▸ pow_orderOf_eq_one t
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact h3

theorem ne_inv_of_orderOf_eq_three {t : A} (ht : orderOf t = 3) : t ≠ t⁻¹ := by
  intro h
  have h2 : t ^ 2 = 1 := by rw [pow_two]; nth_rw 2 [h]; exact mul_inv_cancel t
  have := orderOf_dvd_of_pow_eq_one h2
  rw [ht] at this
  norm_num at this

theorem mem_normalizer_zpowers_iff {t y : A} (ht : orderOf t = 3) :
    y ∈ normalizer (zpowers t : Set A) ↔ y * t * y⁻¹ = t ∨ y * t * y⁻¹ = t⁻¹ := by
  constructor
  · intro hy
    have hmem : y * t * y⁻¹ ∈ zpowers t :=
      (Subgroup.mem_normalizer_iff.mp hy t).mp (mem_zpowers t)
    rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers ht hmem with h1 | h1 | h1
    · exfalso
      have : t = 1 := by
        rw [mul_inv_eq_one, mul_eq_left] at h1
        exact h1
      rw [this, orderOf_one] at ht
      norm_num at ht
    · exact Or.inl h1
    · exact Or.inr h1
  · intro h
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    show zpowers (y * t * y⁻¹) = zpowers t
    rcases h with h | h
    · rw [h]
    · rw [h, Subgroup.zpowers_inv]

theorem centralizer_le_normalizer_zpowers (t : A) :
    centralizer ({t} : Set A) ≤ normalizer (zpowers t : Set A) := by
  intro x hx
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure] at hx
  exact Subgroup.centralizer_le_normalizer _ hx

theorem relIndex_centralizer_normalizer {t u : A} (ht : orderOf t = 3)
    (hu : u * t * u⁻¹ = t⁻¹) :
    (centralizer ({t} : Set A)).relIndex (normalizer (zpowers t : Set A)) = 2 := by
  have htt := ne_inv_of_orderOf_eq_three ht
  have huN : u ∈ normalizer (zpowers t : Set A) := (mem_normalizer_zpowers_iff ht).2 (Or.inr hu)
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨⟨u, huN⟩, ?_, fun b => ?_⟩
  · rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    intro h
    apply htt
    rw [← hu]
    show t = u * t * u⁻¹
    rw [h, mul_inv_cancel_right]
  · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_mul]
    rcases (mem_normalizer_zpowers_iff ht).1 b.2 with hb | hb
    · right
      calc (b : A) * t = (b * t * (b : A)⁻¹) * b := by group
        _ = t * b := by rw [hb]
    · left
      have : (b : A) * u * t * ((b : A) * u)⁻¹ = t := by
        calc (b : A) * u * t * ((b : A) * u)⁻¹ = b * (u * t * u⁻¹) * (b : A)⁻¹ := by group
          _ = (b * t * (b : A)⁻¹)⁻¹ := by rw [hu]; group
          _ = t := by rw [hb, inv_inv]
      calc (b : A) * u * t = ((b : A) * u * t * ((b : A) * u)⁻¹) * ((b : A) * u) := by group
        _ = t * ((b : A) * u) := by rw [this]

theorem mul_comm_of_le_centralizer {t : A} {K : Subgroup A}
    (hK : K ≤ centralizer ({t} : Set A)) : ∀ a ∈ K, ∀ b ∈ zpowers t, a * b = b * a := by
  intro a ha b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hK ha)) k).eq

theorem exists_mul_zpow_of_mem_centralizer {t x : A} {K : Subgroup A}
    (hsup : K ⊔ zpowers t = centralizer ({t} : Set A)) (hx : x ∈ centralizer ({t} : Set A)) :
    ∃ k ∈ K, ∃ i : ℤ, x = k * t ^ i := by
  have hK : K ≤ centralizer ({t} : Set A) := hsup ▸ le_sup_left
  rw [← hsup] at hx
  obtain ⟨a, b, hab⟩ :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81.mem_sup_of_commute_aux (mul_comm_of_le_centralizer hK) hx
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp b.2
  exact ⟨a, a.2, i, by rw [← hab, hi]⟩

theorem eq_of_mul_zpow_eq {t k₁ k₂ : A} {K : Subgroup A} (hinf : K ⊓ zpowers t = ⊥)
    (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K) {i j : ℤ} (h : k₁ * t ^ i = k₂ * t ^ j) :
    k₁ = k₂ ∧ t ^ i = t ^ j := by
  have hmem : k₂⁻¹ * k₁ ∈ K ⊓ zpowers t := by
    refine ⟨K.mul_mem (K.inv_mem hk₂) hk₁, ?_⟩
    have : k₂⁻¹ * k₁ = t ^ j * (t ^ i)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    rw [this]
    exact (zpowers t).mul_mem (zpow_mem_zpowers t j) ((zpowers t).inv_mem (zpow_mem_zpowers t i))
  rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  subst hmem
  exact ⟨rfl, mul_left_cancel h⟩

theorem mem_of_mem_centralizer_of_pow_eq_one {t x : A} {K : Subgroup A} (ht : orderOf t = 3)
    (hinf : K ⊓ zpowers t = ⊥) (hsup : K ⊔ zpowers t = centralizer ({t} : Set A))
    (hx : x ∈ centralizer ({t} : Set A)) {n : ℕ} (hn : x ^ n = 1) (h3 : ¬ 3 ∣ n) : x ∈ K := by
  have hK : K ≤ centralizer ({t} : Set A) := hsup ▸ le_sup_left
  obtain ⟨k, hk, i, rfl⟩ := exists_mul_zpow_of_mem_centralizer hsup hx
  have hc : Commute k (t ^ i) :=
    Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hK hk)) i
  rw [hc.mul_pow] at hn
  have hmem : (t ^ i) ^ n ∈ K ⊓ zpowers t := by
    refine ⟨?_, Subgroup.pow_mem _ (zpow_mem_zpowers t i) n⟩
    rw [eq_inv_of_mul_eq_one_right hn]
    exact K.inv_mem (K.pow_mem hk n)
  rw [hinf, Subgroup.mem_bot] at hmem
  have h1 : orderOf (t ^ i) ∣ n := orderOf_dvd_of_pow_eq_one hmem
  have h2 : orderOf (t ^ i) ∣ 3 := ht ▸ orderOf_dvd_of_mem_zpowers (zpow_mem_zpowers t i)
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have h3' : orderOf (t ^ i) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
  rw [orderOf_eq_one_iff] at h3'
  rw [h3', mul_one]
  exact hk

theorem mem_normalizer_centralizer {t u : A} (ht : orderOf t = 3)
    (hu : u ∈ normalizer (zpowers t : Set A)) :
    u ∈ normalizer (centralizer ({t} : Set A) : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [Subgroup.mem_centralizer_singleton_iff]
  have key : Commute h t ↔ Commute (u * h * u⁻¹) (u * t * u⁻¹) := (Commute.conj_iff u).symm
  rcases (mem_normalizer_zpowers_iff ht).1 hu with hut | hut
  · rw [hut] at key
    exact key
  · rw [hut, Commute.inv_right_iff] at key
    exact key

theorem mem_normalizer_commutator_centralizer {t u : A} (ht : orderOf t = 3)
    (hu : u ∈ normalizer (zpowers t : Set A)) :
    u ∈ normalizer ((⁅centralizer ({t} : Set A), centralizer ({t} : Set A)⁆ :
      Subgroup A) : Set A) := by
  have hC := mem_normalizer_centralizer ht hu
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hC ⊢
  rw [Subgroup.map_commutator, hC]

theorem conj_zpow_of_conj_eq_inv {t u : A} (hu : u * t * u⁻¹ = t⁻¹) (i : ℤ) :
    u * t ^ i * u⁻¹ = t ^ (-i) := by
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hu, inv_zpow']

theorem eight_dvd_card_of_inner [Finite A] {t u z : A} {K : Subgroup A} (ht : orderOf t = 3)
    (hu : u * t * u⁻¹ = t⁻¹) (hinf : K ⊓ zpowers t = ⊥)
    (hsup : K ⊔ zpowers t = centralizer ({t} : Set A))
    (hZ : ∀ k ∈ K, (∀ x ∈ K, k * x = x * k) → k = 1) (hz : z ∈ K) (hz2 : orderOf z = 2)
    (hinner : ∃ k ∈ K, ∀ x ∈ K, u * x * u⁻¹ = k * x * k⁻¹) :
    8 ∣ Nat.card {x : ↥(centralizer ({z} : Set A) ⊓ normalizer (zpowers t : Set A)) //
      x ^ 2 = 1} := by
  classical
  obtain ⟨k, hk, hkx⟩ := hinner
  have hK : K ≤ centralizer ({t} : Set A) := hsup ▸ le_sup_left
  set w := k⁻¹ * u with hw
  have hwK : ∀ x ∈ K, w * x = x * w := by
    intro x hx
    have h := hkx x hx
    calc w * x = k⁻¹ * (u * x * u⁻¹) * u := by rw [hw]; group
      _ = x * w := by rw [h, hw]; group
  have hkt : k * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp (hK hk)
  have hwt : w * t * w⁻¹ = t⁻¹ := by
    calc w * t * w⁻¹ = k⁻¹ * (u * t * u⁻¹) * k := by rw [hw]; group
      _ = (k⁻¹ * t * k)⁻¹ := by rw [hu]; group
      _ = t⁻¹ := by rw [show k⁻¹ * t * k = t by rw [mul_assoc, ← hkt]; group]
  have hw2 : w * w = 1 := by
    have hwwC : w * w ∈ centralizer ({t} : Set A) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc w * w * t = w * (w * t * w⁻¹) * w := by group
        _ = w * t⁻¹ * w := by rw [hwt]
        _ = (w * t * w⁻¹)⁻¹ * (w * w) := by group
        _ = t * (w * w) := by rw [hwt, inv_inv]
    obtain ⟨c, hc, i, hci⟩ := exists_mul_zpow_of_mem_centralizer hsup hwwC
    have hcK : ∀ x ∈ K, c * x = x * c := by
      intro x hx
      have hxt : x * t ^ i = t ^ i * x :=
        (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hK hx)) i).eq
      have h1 : w * w * x = x * (w * w) := by
        calc w * w * x = w * (w * x) := by group
          _ = x * (w * w) := by rw [hwK x hx, ← mul_assoc, hwK x hx, mul_assoc]
      rw [hci] at h1
      have h2 : c * x * t ^ i = x * c * t ^ i := by
        calc c * x * t ^ i = c * (x * t ^ i) := by group
          _ = c * t ^ i * x := by rw [hxt]; group
          _ = x * (c * t ^ i) := h1
          _ = x * c * t ^ i := by group
      exact mul_right_cancel h2
    have hc1 : c = 1 := hZ c hc hcK
    rw [hc1, one_mul] at hci
    have h1 : w * (w * w) * w⁻¹ = w * w := by group
    rw [hci, conj_zpow_of_conj_eq_inv hwt] at h1
    have h2 : (t ^ i) ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [← h1]
      rw [← zpow_add, neg_add_cancel, zpow_zero]
    have h3 : (t ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ht,
        pow_orderOf_eq_one, one_zpow]
    have h4 := Nat.eq_one_of_dvd_coprimes (a := 3) (b := 2) (by norm_num)
      (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
    rw [orderOf_eq_one_iff] at h4
    rw [hci, h4]
  have hwinv : w⁻¹ = w := (eq_inv_of_mul_eq_one_left hw2).symm
  have hzt : z * t = t * z := Subgroup.mem_centralizer_singleton_iff.mp (hK hz)
  have hwz : w * z = z * w := hwK z hz
  have hwt' : ∀ a : ℕ, w * t ^ a = (t ^ a)⁻¹ * w := by
    intro a
    have : w * t ^ a * w⁻¹ = (t ^ a)⁻¹ := by
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hwt, inv_pow]
    calc w * t ^ a = (w * t ^ a * w⁻¹) * w := by group
      _ = (t ^ a)⁻¹ * w := by rw [this]
  have hsq : ∀ x ∈ K, ∀ a : ℕ, (x * t ^ a * w) * (x * t ^ a * w) = x * x := by
    intro x hx a
    have hxw : w * x = x * w := hwK x hx
    have hxt : x * t ^ a = t ^ a * x :=
      (Commute.pow_right (Subgroup.mem_centralizer_singleton_iff.mp (hK hx)) a).eq
    calc (x * t ^ a * w) * (x * t ^ a * w) = x * t ^ a * (w * x) * t ^ a * w := by group
      _ = x * t ^ a * x * (w * t ^ a) * w := by rw [hxw]; group
      _ = x * t ^ a * x * (t ^ a)⁻¹ * (w * w) := by rw [hwt' a]; group
      _ = x * (t ^ a * x) * (t ^ a)⁻¹ := by rw [hw2]; group
      _ = x * x := by rw [← hxt]; group
  have hnotC : ∀ x ∈ K, ∀ a : ℕ, x * t ^ a * w ∉ centralizer ({t} : Set A) := by
    intro x hx a hC
    rw [Subgroup.mem_centralizer_singleton_iff] at hC
    have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (hK hx)
    have hxta : x * t ^ a = t ^ a * x :=
      (Commute.pow_right (Subgroup.mem_centralizer_singleton_iff.mp (hK hx)) a).eq
    have h1 : x * t ^ a * w * t * (x * t ^ a * w)⁻¹ = t⁻¹ := by
      calc x * t ^ a * w * t * (x * t ^ a * w)⁻¹
          = x * t ^ a * (w * t * w⁻¹) * (t ^ a)⁻¹ * x⁻¹ := by group
        _ = x * (t ^ a * t⁻¹ * (t ^ a)⁻¹) * x⁻¹ := by rw [hwt]; group
        _ = x * t⁻¹ * x⁻¹ := by group
        _ = t⁻¹ := by
          rw [(Commute.inv_right (show Commute x t from hxt)).eq, mul_inv_cancel_right]
    rw [hC, mul_inv_cancel_right] at h1
    exact ne_inv_of_orderOf_eq_three ht h1
  set L : Subgroup A := K ⊓ centralizer ({z} : Set A) with hL
  set H : Subgroup A := centralizer ({z} : Set A) ⊓ normalizer (zpowers t : Set A) with hH
  have htC : t ∈ centralizer ({z} : Set A) := Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  have hwC : w ∈ centralizer ({z} : Set A) := Subgroup.mem_centralizer_singleton_iff.mpr hwz
  have hwN : w ∈ normalizer (zpowers t : Set A) := (mem_normalizer_zpowers_iff ht).2 (Or.inr hwt)
  have htN : t ∈ normalizer (zpowers t : Set A) :=
    centralizer_le_normalizer_zpowers t (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hLH : ∀ x ∈ L, x ∈ H := fun x hx =>
    ⟨hx.2, centralizer_le_normalizer_zpowers t (hK hx.1)⟩
  have hmemH : ∀ x ∈ L, ∀ a : ℕ, x * t ^ a * w ∈ H := by
    intro x hx a
    exact H.mul_mem (H.mul_mem (hLH x hx) (H.pow_mem ⟨htC, htN⟩ a)) ⟨hwC, hwN⟩
  let F : {x : ↥L // x * x = 1} × Option (Fin 3) → {y : ↥H // y ^ 2 = 1} := fun p =>
    match p.2 with
    | none => ⟨⟨p.1.1, hLH _ p.1.1.2⟩, by
        apply Subtype.ext
        show ((p.1.1 : ↥L) : A) ^ 2 = 1
        rw [pow_two]
        exact congrArg Subtype.val p.1.2⟩
    | some a => ⟨⟨p.1.1 * t ^ (a : ℕ) * w, hmemH _ p.1.1.2 a⟩, by
        apply Subtype.ext
        show (((p.1.1 : ↥L) : A) * t ^ (a : ℕ) * w) ^ 2 = 1
        rw [pow_two, hsq _ p.1.1.2.1 a]
        exact congrArg Subtype.val p.1.2⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨x, i⟩ ⟨x', j⟩ hxy
      have hval := congrArg (fun y : {y : ↥H // y ^ 2 = 1} => ((y.1 : ↥H) : A)) hxy
      rcases i with _ | a <;> rcases j with _ | b
      · simp only [F] at hval
        exact Prod.ext (Subtype.ext (Subtype.ext hval)) rfl
      · simp only [F] at hval
        exact absurd (hval ▸ hK x.1.2.1) (hnotC _ x'.1.2.1 b)
      · simp only [F] at hval
        exact absurd (hval.symm ▸ hK x'.1.2.1) (hnotC _ x.1.2.1 a)
      · simp only [F] at hval
        have h1 : (x.1 : A) * t ^ ((a : ℕ) : ℤ) = (x'.1 : A) * t ^ ((b : ℕ) : ℤ) := by
          rw [zpow_natCast, zpow_natCast]
          exact mul_right_cancel hval
        obtain ⟨h2, h3⟩ := eq_of_mul_zpow_eq hinf x.1.2.1 x'.1.2.1 h1
        rw [zpow_natCast, zpow_natCast] at h3
        have hab : (a : ℕ) = b := pow_injOn_Iio_orderOf (by rw [ht]; exact a.2)
          (by rw [ht]; exact b.2) h3
        exact Prod.ext (Subtype.ext (Subtype.ext h2)) (by rw [Fin.ext hab])
    · rintro ⟨⟨y, hyC, hyN⟩, hy2⟩
      have hy2' : y * y = 1 := by
        have := congrArg Subtype.val hy2
        rw [pow_two] at this
        exact this
      by_cases hyt : y ∈ centralizer ({t} : Set A)
      · have hyK : y ∈ K := mem_of_mem_centralizer_of_pow_eq_one (n := 2) ht hinf hsup hyt
          (by rw [pow_two]; exact hy2') (by norm_num)
        exact ⟨(⟨⟨y, hyK, hyC⟩, Subtype.ext hy2'⟩, none), rfl⟩
      · have hyinv : y * t * y⁻¹ = t⁻¹ := by
          rcases (mem_normalizer_zpowers_iff ht).1 hyN with h | h
          · exfalso
            apply hyt
            rw [Subgroup.mem_centralizer_singleton_iff]
            calc y * t = (y * t * y⁻¹) * y := by group
              _ = t * y := by rw [h]
          · exact h
        have hywC : y * w ∈ centralizer ({t} : Set A) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have : y * w * t * (y * w)⁻¹ = t := by
            calc y * w * t * (y * w)⁻¹ = y * (w * t * w⁻¹) * y⁻¹ := by group
              _ = (y * t * y⁻¹)⁻¹ := by rw [hwt]; group
              _ = t := by rw [hyinv, inv_inv]
          calc y * w * t = (y * w * t * (y * w)⁻¹) * (y * w) := by group
            _ = t * (y * w) := by rw [this]
        obtain ⟨c, hc, i, hci⟩ := exists_mul_zpow_of_mem_centralizer hsup hywC
        have hpow : ∃ a : Fin 3, t ^ i = t ^ (a : ℕ) := by
          rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers ht (zpow_mem_zpowers t i) with h | h | h
          · exact ⟨0, by rw [h]; simp⟩
          · exact ⟨1, by rw [h]; simp⟩
          · refine ⟨2, ?_⟩
            rw [h]
            have h3 : t ^ 3 = 1 := ht ▸ pow_orderOf_eq_one t
            show t⁻¹ = t ^ 2
            rw [inv_eq_iff_mul_eq_one, ← pow_succ']
            exact h3
        obtain ⟨a, ha⟩ := hpow
        have hy : y = c * t ^ (a : ℕ) * w := by
          calc y = (y * w) * w := by rw [mul_assoc, hw2, mul_one]
            _ = c * t ^ (a : ℕ) * w := by rw [hci, ha]
        have hcC : c ∈ centralizer ({z} : Set A) := by
          have : c = y * w⁻¹ * (t ^ (a : ℕ))⁻¹ := by rw [hy]; group
          rw [this]
          exact (centralizer ({z} : Set A)).mul_mem
            ((centralizer ({z} : Set A)).mul_mem hyC ((centralizer ({z} : Set A)).inv_mem hwC))
            ((centralizer ({z} : Set A)).inv_mem ((centralizer ({z} : Set A)).pow_mem htC _))
        have hc2 : c * c = 1 := by rw [← hsq c hc a, ← hy, hy2']
        refine ⟨(⟨⟨c, hc, hcC⟩, Subtype.ext hc2⟩, some a), ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        show c * t ^ (a : ℕ) * w = y
        exact hy.symm
  have hcard : Nat.card {y : ↥H // y ^ 2 = 1} = Nat.card {x : ↥L // x * x = 1} * 4 := by
    rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_prod, Finite.card_option,
      Nat.card_fin]
  have hzL : z ∈ L := ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hevenL : Even (Nat.card ↥L) := by
    have h := Subgroup.orderOf_dvd_natCard L hzL
    rw [hz2] at h
    exact even_iff_two_dvd.mpr h
  obtain ⟨m, hm⟩ := CFSG.EvenSporadicStandard.M23Std.even_card_sq_eq_one hevenL
  rw [hcard, hm]
  exact ⟨m, by ring⟩

theorem map_normalizer_zpowers_of_injective {B : Type*} [Group B] {f : B →* A}
    (hf : Function.Injective f) {m : B} (hm : orderOf m = 3) :
    (normalizer (zpowers m : Set B)).map f = f.range ⊓ normalizer (zpowers (f m) : Set A) := by
  have hfm : orderOf (f m) = 3 := by rw [orderOf_injective f hf, hm]
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, ?_⟩
    rw [mem_normalizer_zpowers_iff hm] at hy
    rw [mem_normalizer_zpowers_iff hfm, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    rcases hy with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  · rintro ⟨⟨y, rfl⟩, hx⟩
    refine ⟨y, ?_, rfl⟩
    rw [mem_normalizer_zpowers_iff hfm, ← map_inv, ← map_mul, ← map_mul, ← map_inv] at hx
    rw [mem_normalizer_zpowers_iff hm]
    rcases hx with h | h
    · exact Or.inl (hf h)
    · exact Or.inr (hf h)

theorem card_normalizer_zpowers_eq_two_mul [Finite A] {t u : A} (ht : orderOf t = 3)
    (hu : u * t * u⁻¹ = t⁻¹) :
    Nat.card ↥(normalizer (zpowers t : Set A)) = 2 * Nat.card ↥(centralizer ({t} : Set A)) := by
  have h := Subgroup.relIndex_mul_card (H := centralizer ({t} : Set A))
    (K := normalizer (zpowers t : Set A))
  rw [relIndex_centralizer_normalizer ht hu,
    inf_of_le_left (centralizer_le_normalizer_zpowers t)] at h
  exact h.symm

theorem not_inner_of_not_dvd [Finite A] {B : Type*} [Group B] {f : B →* A}
    (hf : Function.Injective f) {z : A} (hrange : f.range = centralizer ({z} : Set A))
    (hz2 : orderOf z = 2) {tB uB : B} (htB : orderOf tB = 3) (huB : uB * tB * uB⁻¹ = tB⁻¹)
    (hcount : ¬ 8 ∣ Nat.card {x : ↥(normalizer (zpowers tB : Set B)) // x ^ 2 = 1})
    {K : Subgroup A} (hinf : K ⊓ zpowers (f tB) = ⊥)
    (hsup : K ⊔ zpowers (f tB) = centralizer ({f tB} : Set A))
    (hZ : ∀ k ∈ K, (∀ x ∈ K, k * x = x * k) → k = 1) :
    ¬ ∃ k ∈ K, ∀ x ∈ K, f uB * x * (f uB)⁻¹ = k * x * k⁻¹ := by
  intro hinner
  have ht : orderOf (f tB) = 3 := by rw [orderOf_injective f hf, htB]
  have hu : f uB * f tB * (f uB)⁻¹ = (f tB)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, huB, map_inv]
  have hzt : z ∈ centralizer ({f tB} : Set A) := by
    have h : f tB ∈ centralizer ({z} : Set A) := hrange ▸ ⟨tB, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
    exact h.symm
  have hzK : z ∈ K := mem_of_mem_centralizer_of_pow_eq_one (n := 2) ht hinf hsup hzt
    (by rw [← hz2]; exact pow_orderOf_eq_one z) (by norm_num)
  have h8 := eight_dvd_card_of_inner ht hu hinf hsup hZ hzK hz2 hinner
  have hmap := map_normalizer_zpowers_of_injective hf htB
  rw [hrange] at hmap
  have e : ↥(normalizer (zpowers tB : Set B)) ≃*
      ↥(centralizer ({z} : Set A) ⊓ normalizer (zpowers (f tB) : Set A)) :=
    (Subgroup.equivMapOfInjective _ f hf).trans (MulEquiv.subgroupCongr hmap)
  have hc : Nat.card {x : ↥(normalizer (zpowers tB : Set B)) // x ^ 2 = 1} =
      Nat.card {x : ↥(centralizer ({z} : Set A) ⊓ normalizer (zpowers (f tB) : Set A)) //
        x ^ 2 = 1} :=
    Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
      show x ^ 2 = 1 ↔ e x ^ 2 = 1
      rw [← map_pow, MulEquiv.map_eq_one_iff])
  exact hcount (hc ▸ h8)

theorem mul_self_mem_of_inv {t u : A} {K : Subgroup A} (ht : orderOf t = 3)
    (hu : u * t * u⁻¹ = t⁻¹) (hinf : K ⊓ zpowers t = ⊥)
    (hsup : K ⊔ zpowers t = centralizer ({t} : Set A)) (hn : u ∈ normalizer (K : Set A)) :
    u * u ∈ K := by
  have hut : u⁻¹ * t * u = t⁻¹ := by
    have : (u * t * u⁻¹)⁻¹ = t := by rw [hu, inv_inv]
    calc u⁻¹ * t * u = u⁻¹ * (u * t * u⁻¹)⁻¹ * u := by rw [this]
      _ = t⁻¹ := by group
  have hC : u * u ∈ centralizer ({t} : Set A) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * u * t = u * (u * t * u⁻¹) * u := by group
      _ = u * t⁻¹ * u := by rw [hu]
      _ = (u * t * u⁻¹)⁻¹ * (u * u) := by group
      _ = t * (u * u) := by rw [hu, inv_inv]
  obtain ⟨k, hk, i, hki⟩ := exists_mul_zpow_of_mem_centralizer hsup hC
  have hk' : u * k * u⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hn k).mp hk
  have hconj : u * (u * u) * u⁻¹ = u * u := by group
  rw [hki] at hconj
  have hti : u * t ^ i * u⁻¹ = t ^ (-i) := by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hu, inv_zpow']
  have h2 : (u * k * u⁻¹) * t ^ (-i) = k * t ^ i := by
    rw [← hti]
    calc u * k * u⁻¹ * (u * t ^ i * u⁻¹) = u * (k * t ^ i) * u⁻¹ := by group
      _ = k * t ^ i := hconj
  obtain ⟨-, h3⟩ := eq_of_mul_zpow_eq hinf hk' hk h2
  have h4 : t ^ i = 1 := by
    have h5 : (t ^ i) ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [← h3]
      rw [← zpow_add, neg_add_cancel, zpow_zero]
    have h6 : (t ^ i) ^ 3 = 1 := by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, ← ht, pow_orderOf_eq_one, one_zpow]
    have := Nat.eq_one_of_dvd_coprimes (a := 3) (b := 2) (by norm_num)
      (orderOf_dvd_of_pow_eq_one h6) (orderOf_dvd_of_pow_eq_one h5)
    rwa [orderOf_eq_one_iff] at this
  rw [hki, h4, mul_one]
  exact hk

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

theorem exists_centralizer_mulEquiv {t₁ : G₁} {t₂ : G₂} {K₁ : Subgroup G₁}
    {K₂ : Subgroup G₂} (ht₁ : orderOf t₁ = 3) (ht₂ : orderOf t₂ = 3)
    (hinf₁ : K₁ ⊓ zpowers t₁ = ⊥) (hsup₁ : K₁ ⊔ zpowers t₁ = centralizer ({t₁} : Set G₁))
    (hinf₂ : K₂ ⊓ zpowers t₂ = ⊥) (hsup₂ : K₂ ⊔ zpowers t₂ = centralizer ({t₂} : Set G₂))
    (κ : ↥K₁ ≃* ↥K₂) :
    ∃ Φ : ↥(centralizer ({t₁} : Set G₁)) ≃* ↥(centralizer ({t₂} : Set G₂)),
      ∀ (x : ↥K₁) (i : ℤ) (y : ↥(centralizer ({t₁} : Set G₁))), (y : G₁) = x * t₁ ^ i →
        (Φ y : G₂) = κ x * t₂ ^ i := by
  have hK₁ : K₁ ≤ centralizer ({t₁} : Set G₁) := hsup₁ ▸ le_sup_left
  have hK₂ : K₂ ≤ centralizer ({t₂} : Set G₂) := hsup₂ ▸ le_sup_left
  have hg₁ : ∀ x : ↥(zpowers t₁), x ∈ zpowers (⟨t₁, mem_zpowers t₁⟩ : ↥(zpowers t₁)) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ⟨k, Subtype.ext (by simp)⟩
  have hg₂ : ∀ x : ↥(zpowers t₂), x ∈ zpowers (⟨t₂, mem_zpowers t₂⟩ : ↥(zpowers t₂)) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ⟨k, Subtype.ext (by simp)⟩
  let φ₂ : ↥(zpowers t₁) ≃* ↥(zpowers t₂) := mulEquivOfOrderOfEq hg₁ hg₂
    (by rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, ht₁, ht₂])
  have hφ₂ : ∀ i : ℤ, ((φ₂ ⟨t₁ ^ i, zpow_mem_zpowers t₁ i⟩ : ↥(zpowers t₂)) : G₂) = t₂ ^ i := by
    intro i
    have h : (⟨t₁ ^ i, zpow_mem_zpowers t₁ i⟩ : ↥(zpowers t₁)) =
        (⟨t₁, mem_zpowers t₁⟩ : ↥(zpowers t₁)) ^ i := Subtype.ext (by simp)
    rw [h, map_zpow, mulEquivOfOrderOfEq_apply_gen]
    simp
  have hZ : ∀ (a : ↥K₁) (b : ↥(zpowers t₁)), (a : G₁) = (b : G₁) →
      ((κ a : ↥K₂) : G₂) = ((φ₂ b : ↥(zpowers t₂)) : G₂) := by
    intro a b hab
    have ha : (a : G₁) ∈ K₁ ⊓ zpowers t₁ := ⟨a.2, hab ▸ b.2⟩
    rw [hinf₁, Subgroup.mem_bot] at ha
    have ha1 : a = 1 := Subtype.ext ha
    have hb1 : b = 1 := Subtype.ext (by rw [← hab, ha]; rfl)
    rw [ha1, hb1, map_one, map_one]
    rfl
  have hZ' : ∀ (a : ↥K₁) (b : ↥(zpowers t₁)),
      ((κ a : ↥K₂) : G₂) = ((φ₂ b : ↥(zpowers t₂)) : G₂) → (a : G₁) = (b : G₁) := by
    intro a b hab
    have ha : ((κ a : ↥K₂) : G₂) ∈ K₂ ⊓ zpowers t₂ := ⟨(κ a).2, hab ▸ (φ₂ b).2⟩
    rw [hinf₂, Subgroup.mem_bot] at ha
    have ha1 : κ a = 1 := Subtype.ext ha
    have hb1 : φ₂ b = 1 := Subtype.ext (by rw [← hab, ha]; rfl)
    rw [map_eq_one_iff κ κ.injective] at ha1
    rw [map_eq_one_iff φ₂ φ₂.injective] at hb1
    rw [ha1, hb1]
    rfl
  obtain ⟨φ, hφK, hφT⟩ := CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81.centralProduct_mulEquiv K₁
    (zpowers t₁) K₂ (zpowers t₂) (mul_comm_of_le_centralizer hK₁)
    (mul_comm_of_le_centralizer hK₂) κ φ₂ hZ hZ'
  refine ⟨((MulEquiv.subgroupCongr hsup₁).symm.trans φ).trans (MulEquiv.subgroupCongr hsup₂),
    fun x i y hy => ?_⟩
  have hy' : (MulEquiv.subgroupCongr hsup₁).symm y =
      (⟨(x : G₁), Subgroup.mem_sup_left x.2⟩ : ↥(K₁ ⊔ zpowers t₁)) *
        ⟨t₁ ^ i, Subgroup.mem_sup_right (zpow_mem_zpowers t₁ i)⟩ := Subtype.ext hy
  show ((φ ((MulEquiv.subgroupCongr hsup₁).symm y) : ↥(K₂ ⊔ zpowers t₂)) : G₂) = _
  rw [hy', map_mul, Subgroup.coe_mul, hφK x,
    hφT ⟨t₁ ^ i, zpow_mem_zpowers t₁ i⟩, hφ₂ i]

theorem exists_normalizer_mulEquiv {t₁ u₁ : G₁} {t₂ u₂ : G₂} {K₁ : Subgroup G₁}
    {K₂ : Subgroup G₂} (ht₁ : orderOf t₁ = 3) (ht₂ : orderOf t₂ = 3)
    (hu₁ : u₁ * t₁ * u₁⁻¹ = t₁⁻¹) (hu₂ : u₂ * t₂ * u₂⁻¹ = t₂⁻¹)
    (hinf₁ : K₁ ⊓ zpowers t₁ = ⊥) (hsup₁ : K₁ ⊔ zpowers t₁ = centralizer ({t₁} : Set G₁))
    (hinf₂ : K₂ ⊓ zpowers t₂ = ⊥) (hsup₂ : K₂ ⊔ zpowers t₂ = centralizer ({t₂} : Set G₂))
    (hn₁ : u₁ ∈ normalizer (K₁ : Set G₁)) (hn₂ : u₂ ∈ normalizer (K₂ : Set G₂))
    (hZ₂ : ∀ k ∈ K₂, (∀ x ∈ K₂, k * x = x * k) → k = 1) (κ : ↥K₁ ≃* ↥K₂)
    (hκ : ∀ x y : ↥K₁, (y : G₁) = u₁ * x * u₁⁻¹ → (κ y : G₂) = u₂ * (κ x : G₂) * u₂⁻¹) :
    ∃ φ : ↥(normalizer (zpowers t₁ : Set G₁)) ≃* ↥(normalizer (zpowers t₂ : Set G₂)),
      (∀ y : ↥(normalizer (zpowers t₁ : Set G₁)), (y : G₁) = t₁ → (φ y : G₂) = t₂) ∧
      (∀ y : ↥(normalizer (zpowers t₁ : Set G₁)), (y : G₁) = u₁ → (φ y : G₂) = u₂) ∧
      ∀ (y : ↥(normalizer (zpowers t₁ : Set G₁))) (x : ↥K₁), (y : G₁) = x →
        (φ y : G₂) = κ x := by
  have hK₁ : K₁ ≤ centralizer ({t₁} : Set G₁) := hsup₁ ▸ le_sup_left
  have hK₂ : K₂ ≤ centralizer ({t₂} : Set G₂) := hsup₂ ▸ le_sup_left
  obtain ⟨Φ, hΦ⟩ := exists_centralizer_mulEquiv ht₁ ht₂ hinf₁ hsup₁ hinf₂ hsup₂ κ
  have hu₁N : u₁ ∈ normalizer (zpowers t₁ : Set G₁) :=
    (mem_normalizer_zpowers_iff ht₁).2 (Or.inr hu₁)
  have hu₂N : u₂ ∈ normalizer (zpowers t₂ : Set G₂) :=
    (mem_normalizer_zpowers_iff ht₂).2 (Or.inr hu₂)
  have hσC : ∀ a : ↥(centralizer ({t₁} : Set G₁)),
      u₁ * a * u₁⁻¹ ∈ centralizer ({t₁} : Set G₁) := fun a =>
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer ht₁ hu₁N) a).mp a.2
  have hsq₁ : u₁ * u₁ ∈ K₁ := mul_self_mem_of_inv ht₁ hu₁ hinf₁ hsup₁ hn₁
  have hsq₂ : u₂ * u₂ ∈ K₂ := mul_self_mem_of_inv ht₂ hu₂ hinf₂ hsup₂ hn₂
  let ι₁ : ↥(centralizer ({t₁} : Set G₁)) →* ↥(normalizer (zpowers t₁ : Set G₁)) :=
    Subgroup.inclusion (centralizer_le_normalizer_zpowers t₁)
  let ι₂ : ↥(centralizer ({t₁} : Set G₁)) →* ↥(normalizer (zpowers t₂ : Set G₂)) :=
    (Subgroup.inclusion (centralizer_le_normalizer_zpowers t₂)).comp Φ.toMonoidHom
  have hι₁ : ∀ a, (ι₁ a : G₁) = a := fun a => rfl
  have hι₂ : ∀ a, (ι₂ a : G₂) = Φ a := fun a => rfl
  have hr₁ : ι₁.range = (centralizer ({t₁} : Set G₁)).subgroupOf
      (normalizer (zpowers t₁ : Set G₁)) := Subgroup.inclusion_range _
  have hr₂ : ι₂.range = (centralizer ({t₂} : Set G₂)).subgroupOf
      (normalizer (zpowers t₂ : Set G₂)) := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨a, rfl⟩
      exact (Φ a).2
    · intro hx
      refine ⟨Φ.symm ⟨x, hx⟩, Subtype.ext ?_⟩
      rw [hι₂, MulEquiv.apply_symm_apply]
  have hs₁ : (⟨u₁, hu₁N⟩ : ↥(normalizer (zpowers t₁ : Set G₁))) ∉ ι₁.range := by
    rw [hr₁, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    intro h
    apply ne_inv_of_orderOf_eq_three ht₁
    rw [← hu₁]
    show t₁ = u₁ * t₁ * u₁⁻¹
    rw [h, mul_inv_cancel_right]
  have hs₂ : (⟨u₂, hu₂N⟩ : ↥(normalizer (zpowers t₂ : Set G₂))) ∉ ι₂.range := by
    rw [hr₂, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    intro h
    apply ne_inv_of_orderOf_eq_three ht₂
    rw [← hu₂]
    show t₂ = u₂ * t₂ * u₂⁻¹
    rw [h, mul_inv_cancel_right]
  have hΦK : ∀ x : ↥K₁, (Φ ⟨x, hK₁ x.2⟩ : G₂) = κ x := by
    intro x
    rw [hΦ x 0 ⟨x, hK₁ x.2⟩ (by simp), zpow_zero, mul_one]
  have h₁ : ι₁.range.index = 2 := by
    rw [hr₁]
    exact relIndex_centralizer_normalizer ht₁ hu₁
  have h₂ : ι₂.range.index = 2 := by
    rw [hr₂]
    exact relIndex_centralizer_normalizer ht₂ hu₂
  have hinj₁ : Function.Injective ι₁ := Subgroup.inclusion_injective _
  have hinj₂ : Function.Injective ι₂ :=
    (Subgroup.inclusion_injective (centralizer_le_normalizer_zpowers t₂)).comp Φ.injective
  let σ : ↥(centralizer ({t₁} : Set G₁)) → ↥(centralizer ({t₁} : Set G₁)) :=
    fun a => ⟨u₁ * a * u₁⁻¹, hσC a⟩
  let τ : ↥(centralizer ({t₁} : Set G₁)) := ⟨u₁ * u₁, hK₁ hsq₁⟩
  have hσ₁ : ∀ a, (⟨u₁, hu₁N⟩ : ↥(normalizer (zpowers t₁ : Set G₁))) * ι₁ a *
      (⟨u₁, hu₁N⟩ : ↥(normalizer (zpowers t₁ : Set G₁)))⁻¹ = ι₁ (σ a) :=
    fun a => Subtype.ext rfl
  have hσ₂ : ∀ a, (⟨u₂, hu₂N⟩ : ↥(normalizer (zpowers t₂ : Set G₂))) * ι₂ a *
      (⟨u₂, hu₂N⟩ : ↥(normalizer (zpowers t₂ : Set G₂)))⁻¹ = ι₂ (σ a) := by
    intro a
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hι₂]
    obtain ⟨x, hx, i, hxi⟩ := exists_mul_zpow_of_mem_centralizer hsup₁ a.2
    have hx' : u₁ * x * u₁⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.mp hn₁ x).mp hx
    rw [hΦ ⟨x, hx⟩ i a hxi]
    have hσa : ((σ a : ↥(centralizer ({t₁} : Set G₁))) : G₁) =
        (u₁ * x * u₁⁻¹) * t₁ ^ (-i) := by
      show u₁ * a * u₁⁻¹ = _
      rw [hxi, ← conj_zpow_of_conj_eq_inv hu₁ i]
      group
    rw [hΦ ⟨u₁ * x * u₁⁻¹, hx'⟩ (-i) (σ a) hσa, hκ ⟨x, hx⟩ ⟨u₁ * x * u₁⁻¹, hx'⟩ rfl,
      ← conj_zpow_of_conj_eq_inv hu₂ i]
    group
  have hτ₁ : (⟨u₁, hu₁N⟩ : ↥(normalizer (zpowers t₁ : Set G₁))) * ⟨u₁, hu₁N⟩ = ι₁ τ :=
    Subtype.ext rfl
  have hτ₂ : (⟨u₂, hu₂N⟩ : ↥(normalizer (zpowers t₂ : Set G₂))) * ⟨u₂, hu₂N⟩ = ι₂ τ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hι₂]
    rw [show τ = ⟨((⟨u₁ * u₁, hsq₁⟩ : ↥K₁) : G₁), hK₁ hsq₁⟩ from rfl, hΦK ⟨u₁ * u₁, hsq₁⟩]
    have hcK : (u₂ * u₂)⁻¹ * (κ ⟨u₁ * u₁, hsq₁⟩ : G₂) ∈ K₂ :=
      K₂.mul_mem (K₂.inv_mem hsq₂) (κ _).2
    have hcomm : ∀ y ∈ K₂, (u₂ * u₂)⁻¹ * (κ ⟨u₁ * u₁, hsq₁⟩ : G₂) * y =
        y * ((u₂ * u₂)⁻¹ * (κ ⟨u₁ * u₁, hsq₁⟩ : G₂)) := by
      intro y hy
      obtain ⟨x, hx⟩ := κ.surjective ⟨y, hy⟩
      have hx1 : u₁ * x * u₁⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.mp hn₁ x).mp x.2
      have hx2 : u₁ * (u₁ * x * u₁⁻¹) * u₁⁻¹ ∈ K₁ :=
        (Subgroup.mem_normalizer_iff.mp hn₁ _).mp hx1
      have e1 := hκ x ⟨_, hx1⟩ rfl
      have e2 := hκ ⟨_, hx1⟩ ⟨_, hx2⟩ rfl
      have e3 : (⟨_, hx2⟩ : ↥K₁) = ⟨u₁ * u₁, hsq₁⟩ * x * (⟨u₁ * u₁, hsq₁⟩ : ↥K₁)⁻¹ :=
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
      have e4 := congrArg (fun w : ↥K₁ => ((κ w : ↥K₂) : G₂)) e3
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at e4
      rw [e2, e1] at e4
      have hy' : y = (κ x : G₂) := by rw [hx]
      rw [hy']
      calc (u₂ * u₂)⁻¹ * (κ ⟨u₁ * u₁, hsq₁⟩ : G₂) * (κ x : G₂)
          = (u₂ * u₂)⁻¹ * ((κ ⟨u₁ * u₁, hsq₁⟩ : G₂) * (κ x : G₂) *
              (κ ⟨u₁ * u₁, hsq₁⟩ : G₂)⁻¹) * (κ ⟨u₁ * u₁, hsq₁⟩ : G₂) := by group
        _ = (u₂ * u₂)⁻¹ * (u₂ * (u₂ * (κ x : G₂) * u₂⁻¹) * u₂⁻¹) *
              (κ ⟨u₁ * u₁, hsq₁⟩ : G₂) := by rw [← e4]
        _ = (κ x : G₂) * ((u₂ * u₂)⁻¹ * (κ ⟨u₁ * u₁, hsq₁⟩ : G₂)) := by group
    have hc1 := hZ₂ _ hcK hcomm
    rw [inv_mul_eq_one] at hc1
    exact hc1
  obtain ⟨e, he, hes⟩ := CFSG.Monster.B.Recog.exists_mulEquiv_of_index_two_of_eq ι₁ ι₂ hinj₁
    hinj₂ h₁ h₂ hs₁ hs₂ σ τ hσ₁ hσ₂ hτ₁ hτ₂
  refine ⟨e, fun y hy => ?_, fun y hy => ?_, fun y x hy => ?_⟩
  · have : y = ι₁ ⟨t₁, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ := Subtype.ext hy
    rw [this, he, hι₂, hΦ 1 1 _ (by simp)]
    simp
  · have : y = ⟨u₁, hu₁N⟩ := Subtype.ext hy
    rw [this, hes]
  · have : y = ι₁ ⟨x, hK₁ x.2⟩ := Subtype.ext hy
    rw [this, he, hι₂, hΦK]

theorem exists_inv_mulEquiv {t u : A} {K : Subgroup A} (ht : orderOf t = 3)
    (hu : u * t * u⁻¹ = t⁻¹) (hinf : K ⊓ zpowers t = ⊥)
    (hsup : K ⊔ zpowers t = centralizer ({t} : Set A)) (hn : u ∈ normalizer (K : Set A))
    (hZ : ∀ k ∈ K, (∀ x ∈ K, k * x = x * k) → k = 1) :
    ∃ ι : ↥(normalizer (zpowers t : Set A)) ≃* ↥(normalizer (zpowers t : Set A)),
      (∀ y : ↥(normalizer (zpowers t : Set A)), (y : A) ∈ K → ι y = y) ∧
      (∀ y : ↥(normalizer (zpowers t : Set A)), (y : A) = t → (ι y : A) = t⁻¹) ∧
      ∀ y : ↥(normalizer (zpowers t : Set A)), (y : A) = u → ι y = y := by
  have ht' : orderOf t⁻¹ = 3 := by rw [orderOf_inv, ht]
  have hu' : u * t⁻¹ * u⁻¹ = t⁻¹⁻¹ := by
    rw [inv_inv]
    calc u * t⁻¹ * u⁻¹ = (u * t * u⁻¹)⁻¹ := by group
      _ = t := by rw [hu, inv_inv]
  have hzi : zpowers t⁻¹ = zpowers t := Subgroup.zpowers_inv
  have hci : centralizer ({t⁻¹} : Set A) = centralizer ({t} : Set A) := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    exact Commute.inv_right_iff
  have hinf' : K ⊓ zpowers t⁻¹ = ⊥ := by rw [hzi]; exact hinf
  have hsup' : K ⊔ zpowers t⁻¹ = centralizer ({t⁻¹} : Set A) := by rw [hzi, hci]; exact hsup
  obtain ⟨φ, hφt, hφu, hφK⟩ := exists_normalizer_mulEquiv ht ht' hu hu' hinf hsup hinf' hsup'
    hn hn hZ (MulEquiv.refl K) (fun x y hy => hy)
  have hN : normalizer (zpowers t⁻¹ : Set A) = normalizer (zpowers t : Set A) := by rw [hzi]
  refine ⟨φ.trans (MulEquiv.subgroupCongr hN), fun y hy => Subtype.ext ?_,
    fun y hy => ?_, fun y hy => Subtype.ext ?_⟩
  · show (φ y : A) = y
    rw [hφK y ⟨y, hy⟩ rfl]
    rfl
  · show (φ y : A) = t⁻¹
    exact hφt y hy
  · show (φ y : A) = y
    rw [hφu y hy, hy]

theorem mem_centralizer_iff_of_mulEquiv {t₁ : G₁} {t₂ : G₂}
    (φ : ↥(normalizer (zpowers t₁ : Set G₁)) ≃* ↥(normalizer (zpowers t₂ : Set G₂)))
    (hφ : ∀ y : ↥(normalizer (zpowers t₁ : Set G₁)), (y : G₁) = t₁ → (φ y : G₂) = t₂)
    (y : ↥(normalizer (zpowers t₁ : Set G₁))) :
    (y : G₁) ∈ centralizer ({t₁} : Set G₁) ↔ (φ y : G₂) ∈ centralizer ({t₂} : Set G₂) := by
  let T₁ : ↥(normalizer (zpowers t₁ : Set G₁)) :=
    ⟨t₁, centralizer_le_normalizer_zpowers t₁ (Subgroup.mem_centralizer_singleton_iff.mpr rfl)⟩
  have hT : (φ T₁ : G₂) = t₂ := hφ T₁ rfl
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : y * T₁ = T₁ * y := Subtype.ext h
    have := congrArg (fun w => (φ w : G₂)) h'
    simp only [map_mul, Subgroup.coe_mul, hT] at this
    exact this
  · intro h
    have h' : φ y * φ T₁ = φ T₁ * φ y := Subtype.ext (by simp only [Subgroup.coe_mul, hT]; exact h)
    rw [← map_mul, ← map_mul] at h'
    exact congrArg Subtype.val (φ.injective h')

theorem mem_commutator_iff_of_mulEquiv {t₁ : G₁} {t₂ : G₂}
    (φ : ↥(normalizer (zpowers t₁ : Set G₁)) ≃* ↥(normalizer (zpowers t₂ : Set G₂)))
    (hφ : ∀ y : ↥(normalizer (zpowers t₁ : Set G₁)), (y : G₁) = t₁ → (φ y : G₂) = t₂)
    (y : ↥(normalizer (zpowers t₁ : Set G₁))) :
    (y : G₁) ∈ ⁅centralizer ({t₁} : Set G₁), centralizer ({t₁} : Set G₁)⁆ ↔
      (φ y : G₂) ∈ ⁅centralizer ({t₂} : Set G₂), centralizer ({t₂} : Set G₂)⁆ := by
  set C₁ := (centralizer ({t₁} : Set G₁)).subgroupOf (normalizer (zpowers t₁ : Set G₁))
  set C₂ := (centralizer ({t₂} : Set G₂)).subgroupOf (normalizer (zpowers t₂ : Set G₂))
  have hmapC : C₁.map φ.toMonoidHom = C₂ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_centralizer_iff_of_mulEquiv φ hφ y).1 hy
    · intro hx
      refine ⟨φ.symm x, ?_, by simp⟩
      show ((φ.symm x : ↥(normalizer (zpowers t₁ : Set G₁))) : G₁) ∈ centralizer ({t₁} : Set G₁)
      rw [mem_centralizer_iff_of_mulEquiv φ hφ, MulEquiv.apply_symm_apply]
      exact hx
  have hcomm₁ : ⁅C₁, C₁⁆.map (normalizer (zpowers t₁ : Set G₁)).subtype =
      ⁅centralizer ({t₁} : Set G₁), centralizer ({t₁} : Set G₁)⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left (centralizer_le_normalizer_zpowers t₁)]
  have hcomm₂ : ⁅C₂, C₂⁆.map (normalizer (zpowers t₂ : Set G₂)).subtype =
      ⁅centralizer ({t₂} : Set G₂), centralizer ({t₂} : Set G₂)⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left (centralizer_le_normalizer_zpowers t₂)]
  have hmap2 : ⁅C₁, C₁⁆.map φ.toMonoidHom = ⁅C₂, C₂⁆ := by
    rw [Subgroup.map_commutator, hmapC]
  constructor
  · intro hy
    rw [← hcomm₁] at hy
    obtain ⟨y', hy', hyy⟩ := hy
    have : y' = y := Subtype.ext hyy
    subst this
    rw [← hcomm₂, ← hmap2]
    exact ⟨φ y', ⟨y', hy', rfl⟩, rfl⟩
  · intro hy
    rw [← hcomm₂, ← hmap2] at hy
    obtain ⟨z, ⟨y', hy', rfl⟩, hzz⟩ := hy
    have : y' = y := φ.injective (Subtype.ext hzz)
    subst this
    rw [← hcomm₁]
    exact ⟨y', hy', rfl⟩

end CFSG.Sporadic.Th.Recog

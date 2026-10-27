module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.Quasithin.H13.A6

open Subgroup

variable {G : Type*} [Group G]

theorem pow_three_mem_of_conj {I P : Subgroup G}
    (hPn : ∀ x ∈ I, ∀ p ∈ P, x * p * x⁻¹ ∈ P) {v w : G} (hvI : v ∈ I) (hwI : w ∈ I)
    (hv : v * v = 1) (hw : w * w = 1)
    (hgen : ∀ x ∈ I, ∃ i : ℤ, ∃ p ∈ P, x = (v * w) ^ i * p ∨ x = v * (v * w) ^ i * p)
    (h6 : (v * w) ^ (6 : ℤ) ∈ P) {y : G} (hyI : y ∈ I) (hy : w⁻¹ * (y⁻¹ * v * y) ∈ P) :
    (v * w) ^ (3 : ℤ) ∈ P := by
  set r := v * w with hr
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hrI : r ∈ I := I.mul_mem hvI hwI
  have h1 : v * r * v = r⁻¹ := by
    rw [hr, mul_inv_rev, hvinv, hwinv]
    calc v * (v * w) * v = (v * v) * w * v := by group
      _ = w * v := by rw [hv, one_mul]
  have h2 : ∀ i : ℤ, v * r ^ i * v = r ^ (-i) := by
    intro i
    calc v * r ^ i * v = v * r ^ i * v⁻¹ := by rw [hvinv]
      _ = (v * r * v⁻¹) ^ i := (conj_zpow).symm
      _ = (r⁻¹) ^ i := by rw [hvinv, h1]
      _ = r ^ (-i) := by rw [inv_zpow']
  have h3 : ∀ i : ℤ, r ^ (-i) * v * r ^ i = v * r ^ (2 * i) := by
    intro i
    have e : r ^ (-i) = v * r ^ i * v := (h2 i).symm
    rw [e]
    calc v * r ^ i * v * v * r ^ i = v * r ^ i * (v * v) * r ^ i := by group
      _ = v * (r ^ i * r ^ i) := by rw [hv, mul_one, mul_assoc]
      _ = v * r ^ (2 * i) := by rw [← zpow_add, two_mul]
  obtain ⟨i, p, hp, hyx⟩ := hgen y hyI
  have hxI : (v * r ^ (2 * i))⁻¹ ∈ I :=
    I.inv_mem (I.mul_mem hvI (I.zpow_mem hrI _))
  have key : y⁻¹ * v * y = p⁻¹ * (v * r ^ (2 * i)) * p := by
    rcases hyx with rfl | rfl
    · rw [← h3 i]; group
    · rw [← h3 i]
      calc (v * r ^ i * p)⁻¹ * v * (v * r ^ i * p) =
            p⁻¹ * r ^ (-i) * (v⁻¹ * v * v) * r ^ i * p := by
            rw [zpow_neg]; group
        _ = p⁻¹ * (r ^ (-i) * v * r ^ i) * p := by rw [inv_mul_cancel, one_mul]; group
  have hconj : (v * r ^ (2 * i))⁻¹ * (y⁻¹ * v * y) ∈ P := by
    rw [key]
    have h' : (v * r ^ (2 * i))⁻¹ * (p⁻¹ * (v * r ^ (2 * i)) * p) =
        ((v * r ^ (2 * i))⁻¹ * p⁻¹ * (v * r ^ (2 * i))⁻¹⁻¹) * p := by group
    rw [h']
    exact P.mul_mem (hPn _ hxI _ (P.inv_mem hp)) hp
  have h4 : r ^ (1 - 2 * i) ∈ P := by
    have h5 := P.mul_mem hconj (P.inv_mem hy)
    have e : (v * r ^ (2 * i))⁻¹ * (y⁻¹ * v * y) * (w⁻¹ * (y⁻¹ * v * y))⁻¹ =
        r ^ (-(2 * i)) * (v⁻¹ * w) := by
      rw [zpow_neg]; group
    rw [e, hvinv] at h5
    have e2 : r ^ (-(2 * i)) * (v * w) = r ^ (1 - 2 * i) := by
      rw [← hr, ← zpow_add_one]
      congr 1
      ring
    rw [e2] at h5
    exact h5
  have e : r ^ (3 : ℤ) = (r ^ (1 - 2 * i)) ^ (3 : ℤ) * (r ^ (6 : ℤ)) ^ i := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_add]
    congr 1
    ring
  rw [e]
  exact P.mul_mem (P.zpow_mem h4 _) (P.zpow_mem h6 _)

theorem exists_dihedral_form {A B P : Subgroup G}
    (hPn : ∀ x ∈ A ⊔ B, ∀ p ∈ P, x * p * x⁻¹ ∈ P) {v w : G} (hvA : v ∈ A) (hwB : w ∈ B)
    (hv : v * v = 1) (hw : w * w = 1) (hA : ∀ x ∈ A, x ∈ P ∨ v * x ∈ P)
    (hB : ∀ x ∈ B, x ∈ P ∨ w * x ∈ P) :
    ∀ x ∈ A ⊔ B, ∃ i : ℤ, ∃ p ∈ P, x = (v * w) ^ i * p ∨ x = v * (v * w) ^ i * p := by
  set r := v * w with hr
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hvI : v ∈ A ⊔ B := Subgroup.mem_sup_left hvA
  have hwI : w ∈ A ⊔ B := Subgroup.mem_sup_right hwB
  have hrI : r ∈ A ⊔ B := (A ⊔ B).mul_mem hvI hwI
  have h1 : v * r * v = r⁻¹ := by
    rw [hr, mul_inv_rev, hvinv, hwinv]
    calc v * (v * w) * v = (v * v) * w * v := by group
      _ = w * v := by rw [hv, one_mul]
  have h2 : ∀ i : ℤ, v * r ^ i * v = r ^ (-i) := by
    intro i
    calc v * r ^ i * v = v * r ^ i * v⁻¹ := by rw [hvinv]
      _ = (v * r * v⁻¹) ^ i := (conj_zpow).symm
      _ = (r⁻¹) ^ i := by rw [hvinv, h1]
      _ = r ^ (-i) := by rw [inv_zpow']
  have hrv : ∀ i : ℤ, r ^ i * v = v * r ^ (-i) := by
    intro i
    calc r ^ i * v = (v * v) * r ^ i * v := by rw [hv, one_mul]
      _ = v * (v * r ^ i * v) := by group
      _ = v * r ^ (-i) := by rw [h2]
  have hPr : ∀ j : ℤ, ∀ p ∈ P, r ^ (-j) * p * r ^ j ∈ P := fun j p hp => by
    have := hPn _ ((A ⊔ B).zpow_mem hrI (-j)) p hp
    rwa [← zpow_neg, neg_neg] at this
  have hPv : ∀ p ∈ P, v * p * v ∈ P := fun p hp => by
    have := hPn _ hvI p hp
    rwa [hvinv] at this
  have hpv : ∀ p : G, p * v = v * (v * p * v) := fun p => by
    calc p * v = (v * v) * p * v := by rw [hv, one_mul]
      _ = v * (v * p * v) := by group
  let D : Subgroup G :=
    { carrier := {x | ∃ i : ℤ, ∃ p ∈ P, x = r ^ i * p ∨ x = v * r ^ i * p}
      one_mem' := ⟨0, 1, P.one_mem, Or.inl (by simp)⟩
      mul_mem' := by
        rintro x y ⟨i, p, hp, hx⟩ ⟨j, q, hq, hy⟩
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · refine ⟨i + j, r ^ (-j) * p * r ^ j * q, P.mul_mem (hPr j p hp) hq, Or.inl ?_⟩
          rw [zpow_add, zpow_neg]; group
        · refine ⟨j - i, r ^ (-j) * (v * p * v) * r ^ j * q,
            P.mul_mem (hPr j _ (hPv p hp)) hq, Or.inr ?_⟩
          calc r ^ i * p * (v * r ^ j * q) = r ^ i * (p * v) * r ^ j * q := by group
            _ = (r ^ i * v) * (v * p * v) * r ^ j * q := by rw [hpv p]; group
            _ = v * r ^ (-i) * (v * p * v) * r ^ j * q := by rw [hrv i]
            _ = v * r ^ (j - i) * (r ^ (-j) * (v * p * v) * r ^ j * q) := by
              rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg, zpow_neg]; group
        · refine ⟨i + j, r ^ (-j) * p * r ^ j * q, P.mul_mem (hPr j p hp) hq, Or.inr ?_⟩
          rw [zpow_add, zpow_neg]; group
        · refine ⟨j - i, r ^ (-j) * (v * p * v) * r ^ j * q,
            P.mul_mem (hPr j _ (hPv p hp)) hq, Or.inl ?_⟩
          calc v * r ^ i * p * (v * r ^ j * q) = v * r ^ i * (p * v) * r ^ j * q := by group
            _ = v * (r ^ i * v) * (v * p * v) * r ^ j * q := by rw [hpv p]; group
            _ = v * (v * r ^ (-i)) * (v * p * v) * r ^ j * q := by rw [hrv i]
            _ = (v * v) * r ^ (-i) * (v * p * v) * r ^ j * q := by group
            _ = r ^ (j - i) * (r ^ (-j) * (v * p * v) * r ^ j * q) := by
              rw [hv, one_mul, sub_eq_add_neg, add_comm, zpow_add, zpow_neg, zpow_neg]; group
      inv_mem' := by
        rintro x ⟨i, p, hp, hx⟩
        rcases hx with rfl | rfl
        · refine ⟨-i, r ^ (-(-i)) * p⁻¹ * r ^ (-i), hPr (-i) _ (P.inv_mem hp), Or.inl ?_⟩
          rw [neg_neg, zpow_neg]; group
        · refine ⟨i, r ^ (-i) * (v * p⁻¹ * v) * r ^ i, hPr i _ (hPv _ (P.inv_mem hp)), Or.inr ?_⟩
          have e : (v * r ^ i * p)⁻¹ = p⁻¹ * (r ^ (-i) * v) := by
            rw [mul_inv_rev, mul_inv_rev, hvinv, zpow_neg]
          rw [e, hrv (-i), neg_neg]
          calc p⁻¹ * (v * r ^ i) = (p⁻¹ * v) * r ^ i := by group
            _ = v * (v * p⁻¹ * v) * r ^ i := by rw [hpv p⁻¹]
            _ = v * r ^ i * (r ^ (-i) * (v * p⁻¹ * v) * r ^ i) := by rw [zpow_neg]; group }
  have hAD : A ≤ D := by
    intro x hx
    rcases hA x hx with h | h
    · exact ⟨0, x, h, Or.inl (by simp)⟩
    · exact ⟨0, v * x, h, Or.inr (by rw [zpow_zero, mul_one, ← mul_assoc, hv, one_mul])⟩
  have hBD : B ≤ D := by
    intro x hx
    rcases hB x hx with h | h
    · exact ⟨0, x, h, Or.inl (by simp)⟩
    ·
      refine ⟨1, w * x, h, Or.inr ?_⟩
      rw [zpow_one, hr]
      calc x = (v * v) * (w * w) * x := by rw [hv, hw, one_mul, one_mul]
        _ = v * (v * w) * (w * x) := by group
  intro x hx
  exact sup_le hAD hBD hx

namespace DMod

@[expose] def fixMod (Z : Subgroup G) (x : G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (Z : Set G) ∧ g * x * g⁻¹ * x⁻¹ ∈ Z}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hgx⟩ ⟨hh, hhx⟩
    refine ⟨Subgroup.mul_mem _ hg hh, ?_⟩
    have e : g * h * x * (g * h)⁻¹ * x⁻¹ =
        g * (h * x * h⁻¹ * x⁻¹) * g⁻¹ * (g * x * g⁻¹ * x⁻¹) := by group
    rw [e]
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp hg _).mp hhx) hgx
  inv_mem' := by
    rintro g ⟨hg, hgx⟩
    refine ⟨Subgroup.inv_mem _ hg, ?_⟩
    have e : g⁻¹ * x * g⁻¹⁻¹ * x⁻¹ = g⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ * g⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp (Z.inv_mem hgx)

structure Hyp (N Z W A : Subgroup G) (v w : G) : Prop where
  ZW : Z ≤ W
  ZA : Z ≤ A
  WN : W ≤ N
  AN : A ≤ N
  WA : ∀ x ∈ W, x ∈ A → x ∈ Z
  prod : ∀ x ∈ N, ∃ a ∈ W, ∃ b ∈ A, x = a * b
  comm : ∀ x ∈ N, ∀ y ∈ N, x * y * x⁻¹ * y⁻¹ ∈ Z
  vN : ∀ x ∈ N, v * x * v⁻¹ * x⁻¹ ∈ W
  vW : ∀ x ∈ W, v * x * v⁻¹ * x⁻¹ ∈ Z
  wN : ∀ x ∈ N, w * x * w⁻¹ * x⁻¹ ∈ A
  wA : ∀ x ∈ A, w * x * w⁻¹ * x⁻¹ ∈ Z
  vZ : v ∈ Subgroup.normalizer (Z : Set G)
  wZ : w ∈ Subgroup.normalizer (Z : Set G)
  v2 : v * v ∈ N
  w2 : w * w ∈ N
  yA : ∀ a ∈ A, (v * w * v) * a * (v * w * v)⁻¹ ∈ W
  yW : ∀ a ∈ W, (v * w * v)⁻¹ * a * (v * w * v) ∈ A

namespace Hyp

variable {N Z W A : Subgroup G} {v w : G} (h : Hyp N Z W A v w)
include h

theorem ZN : Z ≤ N := h.ZW.trans h.WN

theorem conj_mem {n z : G} (hn : n ∈ N) (hz : z ∈ Z) : n * z * n⁻¹ ∈ Z := by
  have e : n * z * n⁻¹ = (n * z * n⁻¹ * z⁻¹) * z := by group
  rw [e]
  exact Z.mul_mem (h.comm n hn z (h.ZN hz)) hz

theorem conj_v_mem {x : G} (hx : x ∈ N) : v * x * v⁻¹ ∈ N := by
  have e : v * x * v⁻¹ = (v * x * v⁻¹ * x⁻¹) * x := by group
  rw [e]
  exact N.mul_mem (h.WN (h.vN x hx)) hx

theorem conj_w_mem {x : G} (hx : x ∈ N) : w * x * w⁻¹ ∈ N := by
  have e : w * x * w⁻¹ = (w * x * w⁻¹ * x⁻¹) * x := by group
  rw [e]
  exact N.mul_mem (h.AN (h.wN x hx)) hx

theorem conj_inv_mod {g x : G} (hg2 : g * g ∈ N) (hx : g * x * g⁻¹ ∈ N) :
    g⁻¹ * x * g * (g * x * g⁻¹)⁻¹ ∈ Z := by
  have hq : g⁻¹ * x * g ∈ N := by
    have e : g⁻¹ * x * g = (g * g)⁻¹ * (g * x * g⁻¹) * (g * g) := by group
    rw [e]
    exact N.mul_mem (N.mul_mem (N.inv_mem hg2) hx) hg2
  have e : g⁻¹ * x * g * (g * x * g⁻¹)⁻¹ =
      (g⁻¹ * x * g) * (g * g) * (g⁻¹ * x * g)⁻¹ * (g * g)⁻¹ := by group
  rw [e]
  exact h.comm _ hq _ hg2

theorem fix_r {x : G} (hx : x ∈ N) (hr : (v * w) * x * (v * w)⁻¹ * x⁻¹ ∈ Z) : x ∈ Z := by
  have ha := h.wN x hx
  have hb := h.vN x hx
  have hc := h.vN _ (h.AN ha)
  set a := w * x * w⁻¹ * x⁻¹ with ha_def
  set b := v * x * v⁻¹ * x⁻¹ with hb_def
  set c := v * a * v⁻¹ * a⁻¹ with hc_def
  have e : (v * w) * x * (v * w)⁻¹ * x⁻¹ = c * a * b := by
    rw [hc_def, ha_def, hb_def]; group
  rw [e] at hr
  have haW : a ∈ W := by
    have e' : a = c⁻¹ * (c * a * b) * b⁻¹ := by group
    rw [e']
    exact W.mul_mem (W.mul_mem (W.inv_mem hc) (h.ZW hr)) (W.inv_mem hb)
  have haZ : a ∈ Z := h.WA a haW ha
  have hcZ : c ∈ Z := by
    rw [hc_def]
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp h.vZ a).mp haZ) (Z.inv_mem haZ)
  have hbZ : b ∈ Z := by
    have e' : b = a⁻¹ * c⁻¹ * (c * a * b) := by group
    rw [e']
    exact Z.mul_mem (Z.mul_mem (Z.inv_mem haZ) (Z.inv_mem hcZ)) hr
  obtain ⟨p, hp, q, hq, rfl⟩ := h.prod x hx
  have hpN := h.WN hp
  have hqN := h.AN hq
  have hvq : v * q * v⁻¹ * q⁻¹ ∈ Z := by
    have e1 : p * (v * q * v⁻¹ * q⁻¹) * p⁻¹ =
        (v * p * v⁻¹ * p⁻¹)⁻¹ * (v * (p * q) * v⁻¹ * (p * q)⁻¹) := by group
    have h1 : p * (v * q * v⁻¹ * q⁻¹) * p⁻¹ ∈ Z := by
      rw [e1]
      exact Z.mul_mem (Z.inv_mem (h.vW p hp)) hbZ
    have e2 : v * q * v⁻¹ * q⁻¹ = p⁻¹ * (p * (v * q * v⁻¹ * q⁻¹) * p⁻¹) * p⁻¹⁻¹ := by group
    rw [e2]
    exact h.conj_mem (N.inv_mem hpN) h1
  have hwp : w * p * w⁻¹ * p⁻¹ ∈ Z := by
    have hwq := h.wA q hq
    have e1 : w * p * w⁻¹ * p⁻¹ =
        (w * (p * q) * w⁻¹ * (p * q)⁻¹) * (p * (w * q * w⁻¹ * q⁻¹) * p⁻¹)⁻¹ := by group
    rw [e1]
    exact Z.mul_mem haZ (Z.inv_mem (h.conj_mem hpN hwq))
  have hvFq : v ∈ fixMod Z q := ⟨h.vZ, hvq⟩
  have hwFq : w ∈ fixMod Z q := ⟨h.wZ, h.wA q hq⟩
  have hvFp : v ∈ fixMod Z p := ⟨h.vZ, h.vW p hp⟩
  have hwFp : w ∈ fixMod Z p := ⟨h.wZ, hwp⟩
  have hyq : v * w * v ∈ fixMod Z q := (fixMod Z q).mul_mem ((fixMod Z q).mul_mem hvFq hwFq) hvFq
  have hyp : (v * w * v)⁻¹ ∈ fixMod Z p :=
    (fixMod Z p).inv_mem ((fixMod Z p).mul_mem ((fixMod Z p).mul_mem hvFp hwFp) hvFp)
  have hqZ : q ∈ Z := by
    refine h.WA q ?_ hq
    have e1 : q = ((v * w * v) * q * (v * w * v)⁻¹ * q⁻¹)⁻¹ *
        ((v * w * v) * q * (v * w * v)⁻¹) := by
      group
    rw [e1]
    exact W.mul_mem (h.ZW (Z.inv_mem hyq.2)) (h.yA q hq)
  have hpZ : p ∈ Z := by
    refine h.WA p hp ?_
    have h2 := hyp.2
    rw [inv_inv] at h2
    have e1 : p = ((v * w * v)⁻¹ * p * (v * w * v) * p⁻¹)⁻¹ *
        ((v * w * v)⁻¹ * p * (v * w * v)) := by
      group
    rw [e1]
    exact A.mul_mem (h.ZA (Z.inv_mem h2)) (h.yW p hp)
  exact Z.mul_mem hpZ hqZ

theorem fix_v_A {x : G} (hx : x ∈ A) (hv : v * x * v⁻¹ * x⁻¹ ∈ Z) : x ∈ Z := by
  have hvF : v ∈ fixMod Z x := ⟨h.vZ, hv⟩
  have hwF : w ∈ fixMod Z x := ⟨h.wZ, h.wA x hx⟩
  exact h.fix_r (h.AN hx) ((fixMod Z x).mul_mem hvF hwF).2

theorem beta_eq {u x : G} (hu : u ∈ W) (hx : x ∈ A) (hxu : (v * x * v⁻¹ * x⁻¹) * u⁻¹ ∈ Z) :
    x * ((v * w * v)⁻¹ * u⁻¹ * (v * w * v))⁻¹ ∈ Z := by
  have hu' : u⁻¹ ∈ W := W.inv_mem hu
  have hu'N := h.WN hu'
  have ha := h.wN _ hu'N
  have haN := h.AN ha
  have hb := h.vN _ haN
  have hbN := h.WN hb
  have hx'A : (v * w * v)⁻¹ * u⁻¹ * (v * w * v) ∈ A := h.yW _ hu'
  have hvF : v ∈ fixMod Z u⁻¹ := ⟨h.vZ, h.vW _ hu'⟩
  have hz1 : v⁻¹ * u⁻¹ * v⁻¹⁻¹ * u⁻¹⁻¹ ∈ Z := ((fixMod Z u⁻¹).inv_mem hvF).2
  have hz2 := h.conj_inv_mod h.w2 (h.conj_w_mem hu'N)
  have hz3 := h.conj_inv_mod h.v2 (h.conj_v_mem haN)
  set a := w * u⁻¹ * w⁻¹ * u⁻¹⁻¹ with ha_def
  set b := v * a * v⁻¹ * a⁻¹ with hb_def
  set x' := (v * w * v)⁻¹ * u⁻¹ * (v * w * v) with hx'_def
  set z1 := v⁻¹ * u⁻¹ * v⁻¹⁻¹ * u⁻¹⁻¹ with hz1_def
  set z2 := w⁻¹ * u⁻¹ * w * (w * u⁻¹ * w⁻¹)⁻¹ with hz2_def
  set z3 := v⁻¹ * a * v * (v * a * v⁻¹)⁻¹ with hz3_def
  have hZ0 : v⁻¹ * (w⁻¹ * z1 * w⁻¹⁻¹ * z2) * v⁻¹⁻¹ ∈ Z := by
    have hw' : w⁻¹ * z1 * w⁻¹⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ h.wZ) _).mp hz1
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ h.vZ) _).mp (Z.mul_mem hw' hz2)
  have claim1 : x' * (b * a * u⁻¹)⁻¹ ∈ Z := by
    have e : x' * (b * a * u⁻¹)⁻¹ = (v⁻¹ * (w⁻¹ * z1 * w⁻¹⁻¹ * z2) * v⁻¹⁻¹) * z3 *
        ((b * a) * z1 * (b * a)⁻¹) := by
      simp only [hx'_def, hz1_def, hz2_def, hz3_def, hb_def, ha_def]; group
    rw [e]
    exact Z.mul_mem (Z.mul_mem hZ0 hz3) (h.conj_mem (N.mul_mem hbN haN) hz1)
  have claim2 : b * u⁻¹ ∈ Z := by
    have h1 : b * a * u⁻¹ ∈ A := by
      have e : b * a * u⁻¹ = (x' * (b * a * u⁻¹)⁻¹)⁻¹ * x' := by group
      rw [e]
      exact A.mul_mem (h.ZA (Z.inv_mem claim1)) hx'A
    refine h.WA _ (W.mul_mem hb hu') ?_
    have e : b * u⁻¹ = (a⁻¹ * b * a⁻¹⁻¹ * b⁻¹)⁻¹ * (a⁻¹ * (b * a * u⁻¹)) := by group
    rw [e]
    exact A.mul_mem (h.ZA (Z.inv_mem (h.comm _ (N.inv_mem haN) _ hbN)))
      (A.mul_mem (A.inv_mem ha) h1)
  have claim3 : (v * x' * v⁻¹ * x'⁻¹) * u⁻¹ ∈ Z := by
    have hk : x' * a⁻¹ ∈ Z := by
      have e : x' * a⁻¹ = (x' * (b * a * u⁻¹)⁻¹) * (b * (a * u⁻¹ * a⁻¹ * u⁻¹⁻¹) * b⁻¹) *
          (b * u⁻¹) := by group
      rw [e]
      exact Z.mul_mem (Z.mul_mem claim1 (h.conj_mem hbN (h.comm _ haN _ hu'N))) claim2
    have e : (v * x' * v⁻¹ * x'⁻¹) * u⁻¹ =
        (v * (x' * a⁻¹) * v⁻¹) * (b * (x' * a⁻¹)⁻¹ * b⁻¹) * (b * u⁻¹) := by
      rw [hb_def]; group
    rw [e]
    exact Z.mul_mem (Z.mul_mem ((Subgroup.mem_normalizer_iff.mp h.vZ _).mp hk)
      (h.conj_mem hbN (Z.inv_mem hk))) claim2
  have hxN := h.AN hx
  have hx'N := h.AN hx'A
  have hk2 : x * x'⁻¹ ∈ N := N.mul_mem hxN (N.inv_mem hx'N)
  have hmN : (v * x' * v⁻¹ * x'⁻¹)⁻¹ ∈ N := N.inv_mem (h.WN (h.vN _ hx'N))
  refine h.fix_v_A (A.mul_mem hx (A.inv_mem hx'A)) ?_
  have e : v * (x * x'⁻¹) * v⁻¹ * (x * x'⁻¹)⁻¹ = ((v * x * v⁻¹ * x⁻¹) * u⁻¹) *
      (u * ((x * x'⁻¹) * (v * x' * v⁻¹ * x'⁻¹)⁻¹ * (x * x'⁻¹)⁻¹ *
        (v * x' * v⁻¹ * x'⁻¹)⁻¹⁻¹) * u⁻¹) * ((v * x' * v⁻¹ * x'⁻¹) * u⁻¹)⁻¹ := by group
  rw [e]
  exact Z.mul_mem (Z.mul_mem hxu (h.conj_mem (h.WN hu) (h.comm _ hk2 _ hmN)))
    (Z.inv_mem claim3)

end Hyp

end DMod

end CFSG.Quasithin.H13.A6

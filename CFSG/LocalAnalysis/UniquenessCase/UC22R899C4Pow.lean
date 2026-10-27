module

import CFSG.GH74.Uniqueness.SU.SU1Normal2
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem uc22r899c4_exists_pow_of_isCyclic {S : Subgroup Γ} [IsCyclic S] {d : Γ}
    (hd : d ∈ normalizer (S : Set Γ)) : ∃ e : ℕ, ∀ u ∈ S, d * u * d⁻¹ = u ^ e := by
  obtain ⟨⟨s, hs⟩, hgen⟩ := IsCyclic.exists_generator (α := ↥S)
  have hSs : S = zpowers s := by
    refine le_antisymm (fun y hy => ?_) (zpowers_le.2 hs)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨y, hy⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨j, by simpa using congrArg Subtype.val hj⟩
  rw [hSs] at hd ⊢
  have h := (Subgroup.mem_normalizer_iff.mp hd s).mp (Subgroup.mem_zpowers s)
  obtain ⟨k, hk⟩ := (isOfFinOrder_of_finite s).mem_powers_iff_mem_zpowers.mpr h
  exact ⟨k, fun u hu => CFSG.GH74.Uniqueness.SU.SU1.conj_of_mem_zpowers hk.symm hu⟩

theorem uc22r899c4_conj_pow_mul {U : Subgroup Γ} {a b : Γ} {k l : ℕ}
    (ha : ∀ u ∈ U, a * u * a⁻¹ = u ^ k) (hb : ∀ u ∈ U, b * u * b⁻¹ = u ^ l) :
    ∀ u ∈ U, a * b * u * (a * b)⁻¹ = u ^ (k * l) := by
  intro u hu
  calc a * b * u * (a * b)⁻¹ = a * (b * u * b⁻¹) * a⁻¹ := by group
    _ = (a * u * a⁻¹) ^ l := by rw [hb u hu, conj_pow]
    _ = u ^ (k * l) := by rw [ha u hu, ← pow_mul]

theorem uc22r899c4_conj_pow_pow {U : Subgroup Γ} {x : Γ} {k : ℕ}
    (h : ∀ u ∈ U, x * u * x⁻¹ = u ^ k) (m : ℕ) :
    ∀ u ∈ U, x ^ m * u * (x ^ m)⁻¹ = u ^ (k ^ m) := by
  induction m with
  | zero => intro u _; simp
  | succ m ih =>
    intro u hu
    rw [pow_succ x m, pow_succ k m]
    exact uc22r899c4_conj_pow_mul ih h u hu

theorem uc22r899c4_conj_pow_conj {U : Subgroup Γ} {x : Γ} {k : ℕ}
    (h : ∀ u ∈ U, x * u * x⁻¹ = u ^ k) (w : Γ) :
    ∀ u ∈ U.map (MulAut.conj w).toMonoidHom, w * x * w⁻¹ * u * (w * x * w⁻¹)⁻¹ = u ^ k := by
  rintro _ ⟨v, hv, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc w * x * w⁻¹ * (w * v * w⁻¹) * (w * x * w⁻¹)⁻¹ = w * (x * v * x⁻¹) * w⁻¹ := by group
    _ = (w * v * w⁻¹) ^ k := by rw [h v hv, conj_pow]

theorem uc22r899c4_conj_pow_sup {x a b : Γ} {k : ℕ} (hab : a * b = b * a)
    (ha : x * a * x⁻¹ = a ^ k) (hb : x * b * x⁻¹ = b ^ k) :
    ∀ u ∈ zpowers a ⊔ zpowers b, x * u * x⁻¹ = u ^ k := by
  have hcl : zpowers a ⊔ zpowers b = closure {a, b} := by
    rw [zpowers_eq_closure, zpowers_eq_closure, ← Subgroup.closure_union, Set.singleton_union]
  have hpair : ({a, b} : Set Γ).Pairwise Commute := by
    intro u hu v hv _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    exacts [Commute.refl _, hab, hab.symm, Commute.refl _]
  haveI := Subgroup.isMulCommutative_closure hpair
  intro u hu
  rw [hcl] at hu
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    rcases hu with rfl | hu
    · exact ha
    · rw [Set.mem_singleton_iff.1 hu]
      exact hb
  | one => simp
  | mul u v hu hv ihu ihv =>
    have huv : Commute u v := congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : ↥(closure {a, b}))
      ⟨v, hv⟩)
    calc x * (u * v) * x⁻¹ = (x * u * x⁻¹) * (x * v * x⁻¹) := by group
      _ = (u * v) ^ k := by rw [ihu, ihv, huv.mul_pow]
  | inv u hu ihu => rw [inv_pow, ← ihu]; group

def uc22r899c4_powSub (U : Subgroup Γ) : Subgroup Γ where
  carrier := {x | ∃ k : ℕ, ∀ u ∈ U, x * u * x⁻¹ = u ^ k}
  mul_mem' := by
    rintro x y ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k * l, uc22r899c4_conj_pow_mul hk hl⟩
  one_mem' := ⟨1, fun u _ => by simp⟩
  inv_mem' := by
    rintro x ⟨k, hk⟩
    have hx : x ^ (orderOf x - 1) = x⁻¹ :=
      eq_inv_of_mul_eq_one_left (by
        rw [pow_sub_one_mul (orderOf_pos x).ne', pow_orderOf_eq_one])
    refine ⟨k ^ (orderOf x - 1), fun u hu => ?_⟩
    have h := uc22r899c4_conj_pow_pow hk (orderOf x - 1) u hu
    rwa [hx] at h

theorem uc22r899c4_mem_powSub {U : Subgroup Γ} {x : Γ} :
    x ∈ uc22r899c4_powSub U ↔ ∃ k : ℕ, ∀ u ∈ U, x * u * x⁻¹ = u ^ k :=
  Iff.rfl

theorem uc22r899c4_le_normalizer_of_pow {B U H : Subgroup Γ}
    (hB : ∀ b ∈ B, ∃ k : ℕ, ∀ u ∈ U, b * u * b⁻¹ = u ^ k) (hHU : H ≤ U) :
    B ≤ normalizer (H : Set Γ) := by
  intro b hb
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨k, hk⟩ := hB b hb
    rw [hk h (hHU hh)]
    exact H.pow_mem hh k
  · obtain ⟨l, hl⟩ := hB b⁻¹ (B.inv_mem hb)
    have e : h = b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ := by group
    rw [e, hl _ (hHU hh)]
    exact H.pow_mem hh l

theorem uc22r899c4_dvd_orderOf {p r : ℕ} (hp : p.Prime) {t h : Γ} (hto : orderOf t = r) {e : ℕ}
    (he : h * t * h⁻¹ = t ^ e) {ζ : ZMod r} (hζ : orderOf ζ = p) {m : ℕ}
    (hζe : (e : ZMod r) = ζ ^ m) (hm : ¬ p ∣ m) : p ∣ orderOf h := by
  have h1 := uc22r899c4_conj_pow_pow (U := zpowers t)
    (fun u hu => CFSG.GH74.Uniqueness.SU.SU1.conj_of_mem_zpowers he hu) (orderOf h) t
    (mem_zpowers t)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have h2 : e ^ orderOf h ≡ 1 [MOD r] := by
    rw [← hto]
    exact pow_eq_pow_iff_modEq.1 (by rw [pow_one]; exact h1.symm)
  have h3 : ζ ^ (m * orderOf h) = 1 := by
    rw [pow_mul, ← hζe, ← Nat.cast_pow, (ZMod.natCast_eq_natCast_iff _ _ _).2 h2, Nat.cast_one]
  have h4 : p ∣ m * orderOf h := hζ ▸ orderOf_dvd_of_pow_eq_one h3
  exact ((Nat.Prime.dvd_mul hp).1 h4).resolve_left hm

end CFSG.LocalAnalysis.UniquenessCase.UC22

module

public import Mathlib.GroupTheory.Commutator.Basic

import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped commutatorElement

variable {C : Type} [Group C]

theorem commutatorElement_mem_pair_of_mem_closure {S : Set C} {x z : C}
    (hz : ∀ p ∈ Subgroup.closure S, z * p = p * z) (hz2 : z * z = 1)
    (h : ∀ s ∈ S, ⁅x, s⁆ = 1 ∨ ⁅x, s⁆ = z) {p : C} (hp : p ∈ Subgroup.closure S) :
    ⁅x, p⁆ = 1 ∨ ⁅x, p⁆ = z := by
  induction hp using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => exact Or.inl (by rw [commutatorElement_def]; group)
  | mul p q hp _ ihp ihq =>
    have key : ⁅x, p * q⁆ = ⁅x, p⁆ * (p * ⁅x, q⁆ * p⁻¹) := by
      simp only [commutatorElement_def]
      group
    have hc : p * ⁅x, q⁆ * p⁻¹ = ⁅x, q⁆ := by
      rcases ihq with h1 | h1
      · rw [h1]
        group
      · rw [h1, ← hz p hp]
        group
    rw [key, hc]
    rcases ihp with h1 | h1 <;> rcases ihq with h2 | h2 <;> simp [h1, h2, hz2]
  | inv p hp ihp =>
    have key : ⁅x, p⁻¹⁆ = p⁻¹ * ⁅x, p⁆⁻¹ * p := by
      simp only [commutatorElement_def]
      group
    rw [key]
    rcases ihp with h1 | h1
    · exact Or.inl (by rw [h1]; group)
    · refine Or.inr ?_
      rw [h1, inv_eq_of_mul_eq_one_right hz2]
      calc p⁻¹ * z * p = z * p⁻¹ * p := by rw [hz p⁻¹ (inv_mem hp)]
        _ = z := by group

theorem apply_mem_of_forall_mem_iff_commutatorElement {T V : Subgroup C} {z : C}
    (hV : ∀ x, x ∈ V ↔ x ∈ T ∧ ∀ p ∈ T, ⁅x, p⁆ = 1 ∨ ⁅x, p⁆ = z) (φ : C ≃* C)
    (h1 : ∀ y ∈ T, φ y ∈ T) (h2 : ∀ p ∈ T, ∃ q ∈ T, φ q = p) (hφz : φ z = z) {y : C}
    (hy : y ∈ V) : φ y ∈ V := by
  obtain ⟨hyT, hyc⟩ := (hV y).1 hy
  refine (hV _).2 ⟨h1 y hyT, fun p hp => ?_⟩
  obtain ⟨q, hq, rfl⟩ := h2 p hp
  rw [← map_commutatorElement φ y q]
  rcases hyc q hq with h | h
  · exact Or.inl (by rw [h, map_one])
  · exact Or.inr (by rw [h, hφz])

theorem apply_eq_of_center_eq_pair {T : Subgroup C} {z : C} (hzT : z ∈ T) (hz1 : z ≠ 1)
    (hzc : ∀ p ∈ T, z * p = p * z)
    (hZ : ∀ x ∈ T, (∀ p ∈ T, x * p = p * x) → x = 1 ∨ x = z) {ψ : C ≃* C}
    (hψ : T.map ψ.toMonoidHom = T) : ψ z = z := by
  have hmem : ∀ {y : C}, y ∈ T → ψ y ∈ T := fun {y} hy => by
    rw [← hψ]
    exact Subgroup.mem_map.2 ⟨y, hy, rfl⟩
  have hpre : ∀ {p : C}, p ∈ T → ∃ q ∈ T, ψ q = p := fun {p} hp => by
    rw [← hψ] at hp
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hp
    exact ⟨q, hq, rfl⟩
  rcases hZ (ψ z) (hmem hzT) (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := hpre hp
      rw [← map_mul ψ, ← map_mul ψ, hzc q hq]) with h | h
  · exact absurd (ψ.injective (h.trans (map_one ψ).symm)) hz1
  · exact h

theorem map_centralizer_singleton_eq_of_apply_eq {z : C} {ψ : C ≃* C} (h : ψ z = z) :
    (Subgroup.centralizer ({z} : Set C)).map ψ.toMonoidHom = Subgroup.centralizer {z} := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have := congrArg ψ hx
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, h] at this
  · intro hx
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h, hx]

theorem map_centralizer_normalizer_eq_of_center_zTwo {T V : Subgroup C} {z : C} (hzT : z ∈ T)
    (hz1 : z ≠ 1) (hzc : ∀ p ∈ T, z * p = p * z)
    (hZ : ∀ x ∈ T, (∀ p ∈ T, x * p = p * x) → x = 1 ∨ x = z)
    (hV : ∀ x, x ∈ V ↔ x ∈ T ∧ ∀ p ∈ T, ⁅x, p⁆ = 1 ∨ ⁅x, p⁆ = z) (ψ : C ≃* C)
    (hψ : T.map ψ.toMonoidHom = T) :
    (Subgroup.centralizer ({z} : Set C)).map ψ.toMonoidHom = Subgroup.centralizer {z} ∧
      (Subgroup.normalizer (V : Set C)).map ψ.toMonoidHom = Subgroup.normalizer (V : Set C) := by
  have hψz := apply_eq_of_center_eq_pair hzT hz1 hzc hZ hψ
  have hmem : ∀ y ∈ T, ψ y ∈ T := fun y hy => by
    rw [← hψ]
    exact Subgroup.mem_map.2 ⟨y, hy, rfl⟩
  have hpre : ∀ p ∈ T, ∃ q ∈ T, ψ q = p := fun p hp => by
    rw [← hψ] at hp
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hp
    exact ⟨q, hq, rfl⟩
  have hVmap : V.map ψ.toMonoidHom = V := by
    ext x
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro hx
      have := apply_mem_of_forall_mem_iff_commutatorElement hV ψ hmem hpre hψz hx
      rwa [MulEquiv.apply_symm_apply] at this
    · intro hx
      refine apply_mem_of_forall_mem_iff_commutatorElement hV ψ.symm (fun y hy => ?_)
        (fun p hp => ⟨ψ p, hmem p hp, ψ.symm_apply_apply p⟩) ?_ hx
      · obtain ⟨q, hq, rfl⟩ := hpre y hy
        rwa [ψ.symm_apply_apply]
      · rw [MulEquiv.symm_apply_eq]
        exact hψz.symm
  refine ⟨map_centralizer_singleton_eq_of_apply_eq hψz, ?_⟩
  rw [Subgroup.map_equiv_normalizer_eq, hVmap]

@[expose] def zTwoOf (T : Subgroup C) (z : C) (hzc : ∀ p ∈ T, z * p = p * z) (hz2 : z * z = 1) :
    Subgroup C where
  carrier := {x | x ∈ T ∧ ∀ p ∈ T, ⁅x, p⁆ = 1 ∨ ⁅x, p⁆ = z}
  one_mem' := ⟨T.one_mem, fun _ _ => Or.inl (by rw [commutatorElement_def]; group)⟩
  mul_mem' := by
    rintro x y ⟨hxT, hx⟩ ⟨hyT, hy⟩
    refine ⟨T.mul_mem hxT hyT, fun p hp => ?_⟩
    have key : ⁅x * y, p⁆ = x * ⁅y, p⁆ * x⁻¹ * ⁅x, p⁆ := by
      simp only [commutatorElement_def]
      group
    have hc : x * ⁅y, p⁆ * x⁻¹ = ⁅y, p⁆ := by
      rcases hy p hp with h1 | h1
      · rw [h1]
        group
      · rw [h1, ← hzc x hxT]
        group
    rw [key, hc]
    rcases hx p hp with h1 | h1 <;> rcases hy p hp with h2 | h2 <;> simp [h1, h2, hz2]
  inv_mem' := by
    rintro x ⟨hxT, hx⟩
    refine ⟨T.inv_mem hxT, fun p hp => ?_⟩
    have key : ⁅x⁻¹, p⁆ = x⁻¹ * ⁅x, p⁆⁻¹ * x := by
      simp only [commutatorElement_def]
      group
    rw [key]
    rcases hx p hp with h1 | h1
    · exact Or.inl (by rw [h1]; group)
    · refine Or.inr ?_
      rw [h1, inv_eq_of_mul_eq_one_right hz2]
      calc x⁻¹ * z * x = z * x⁻¹ * x := by rw [hzc x⁻¹ (T.inv_mem hxT)]
        _ = z := by group

theorem mem_zTwoOf {T : Subgroup C} {z : C} {hzc : ∀ p ∈ T, z * p = p * z} {hz2 : z * z = 1}
    {x : C} : x ∈ zTwoOf T z hzc hz2 ↔ x ∈ T ∧ ∀ p ∈ T, ⁅x, p⁆ = 1 ∨ ⁅x, p⁆ = z :=
  Iff.rfl

theorem conj_mem_zTwoOf {T : Subgroup C} {z : C} {hzc : ∀ p ∈ T, z * p = p * z}
    {hz2 : z * z = 1} {g : C} (hg : g ∈ T) {x : C} (hx : x ∈ zTwoOf T z hzc hz2) :
    g * x * g⁻¹ ∈ zTwoOf T z hzc hz2 := by
  have h := apply_mem_of_forall_mem_iff_commutatorElement (T := T) (V := zTwoOf T z hzc hz2)
    (z := z) (fun _ => mem_zTwoOf) (MulAut.conj g)
    (fun y hy => by rw [MulAut.conj_apply]; exact T.mul_mem (T.mul_mem hg hy) (T.inv_mem hg))
    (fun p hp => ⟨g⁻¹ * p * g, T.mul_mem (T.mul_mem (T.inv_mem hg) hp) hg,
      by rw [MulAut.conj_apply]; group⟩)
    (by rw [MulAut.conj_apply, ← hzc g hg]; group) hx
  rwa [MulAut.conj_apply] at h

theorem le_normalizer_zTwoOf (T : Subgroup C) (z : C) (hzc : ∀ p ∈ T, z * p = p * z)
    (hz2 : z * z = 1) : T ≤ Subgroup.normalizer (zTwoOf T z hzc hz2 : Set C) := fun g hg =>
  Subgroup.mem_normalizer_iff.2 fun x => ⟨conj_mem_zTwoOf hg, fun h => by
    simpa [mul_assoc] using conj_mem_zTwoOf (T.inv_mem hg) h⟩

theorem map_centralizer_normalizer_zTwoOf_eq {T : Subgroup C} {z : C} (hzT : z ∈ T)
    (hz1 : z ≠ 1) (hzc : ∀ p ∈ T, z * p = p * z) (hz2 : z * z = 1)
    (hZ : ∀ x ∈ T, (∀ p ∈ T, x * p = p * x) → x = 1 ∨ x = z) (ψ : C ≃* C)
    (hψ : T.map ψ.toMonoidHom = T) :
    (Subgroup.centralizer ({z} : Set C)).map ψ.toMonoidHom = Subgroup.centralizer {z} ∧
      (Subgroup.normalizer (zTwoOf T z hzc hz2 : Set C)).map ψ.toMonoidHom =
        Subgroup.normalizer (zTwoOf T z hzc hz2 : Set C) :=
  map_centralizer_normalizer_eq_of_center_zTwo hzT hz1 hzc hZ (fun _ => mem_zTwoOf) ψ hψ

end CFSG.LocalAnalysis.WeakClosure81

end

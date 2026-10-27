module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType

section

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {m : ℕ}

@[expose] def GGCZDual (e : Fin m → V) (φ : Fin m → Module.Dual (ZMod p) V) : Prop :=
  ∀ i j, φ i (e j) = if i = j then 1 else 0

@[expose] def ggCZRD (e : Fin m → V) (φ : Fin m → Module.Dual (ZMod p) V) :
    Set (V ≃ₗ[ZMod p] V) :=
  {r | ∃ i j : Fin m, i ≠ j ∧ ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧
    ∀ v, r v = v - (φ i v - ε * φ j v) • (e i - ε • e j)}

@[expose] def ggCZS (e : Fin m → V) (φ : Fin m → Module.Dual (ZMod p) V) :
    Set (V ≃ₗ[ZMod p] V) :=
  {r | ∃ i : Fin m, ∀ v, r v = v - (2 * φ i v) • e i}

@[expose] def ggCZH (e : Fin m → V) (φ : Fin m → Module.Dual (ZMod p) V) :
    Set (V ≃ₗ[ZMod p] V) :=
  {r | ∃ w : Fin m → ZMod p, (∀ k, w k = 1 ∨ w k = -1) ∧
    ∀ v, r v = v - ((2 : ZMod p)⁻¹ * ∑ k, w k * φ k v) • ∑ k, w k • e k}

@[expose] def ggCZForm (φ : Fin m → Module.Dual (ZMod p) V) (v w : V) : ZMod p :=
  ∑ k, φ k v * φ k w

theorem ggCZForm_comm {φ : Fin m → Module.Dual (ZMod p) V} (v w : V) :
    ggCZForm φ v w = ggCZForm φ w v := by
  simp [ggCZForm, mul_comm]

theorem ggCZForm_add_left {φ : Fin m → Module.Dual (ZMod p) V} (v w x : V) :
    ggCZForm φ (v + w) x = ggCZForm φ v x + ggCZForm φ w x := by
  simp [ggCZForm, Finset.sum_add_distrib, add_mul]

theorem ggCZForm_add_right {φ : Fin m → Module.Dual (ZMod p) V} (v x y : V) :
    ggCZForm φ v (x + y) = ggCZForm φ v x + ggCZForm φ v y := by
  simp [ggCZForm, Finset.sum_add_distrib, mul_add]

theorem ggCZForm_sub_left {φ : Fin m → Module.Dual (ZMod p) V} (v w x : V) :
    ggCZForm φ (v - w) x = ggCZForm φ v x - ggCZForm φ w x := by
  simp [ggCZForm, Finset.sum_sub_distrib, sub_mul]

theorem ggCZForm_sub_right {φ : Fin m → Module.Dual (ZMod p) V} (v x y : V) :
    ggCZForm φ v (x - y) = ggCZForm φ v x - ggCZForm φ v y := by
  simp [ggCZForm, Finset.sum_sub_distrib, mul_sub]

theorem ggCZForm_smul_left {φ : Fin m → Module.Dual (ZMod p) V} (a : ZMod p) (v x : V) :
    ggCZForm φ (a • v) x = a * ggCZForm φ v x := by
  simp [ggCZForm, Finset.mul_sum, mul_assoc]

theorem ggCZForm_smul_right {φ : Fin m → Module.Dual (ZMod p) V} (a : ZMod p) (v x : V) :
    ggCZForm φ v (a • x) = a * ggCZForm φ v x := by
  simp only [ggCZForm, map_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem ggCZForm_apply_e {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (v : V) (k : Fin m) : ggCZForm φ v (e k) = φ k v := by
  have hd' : ∀ i j, φ i (e j) = if i = j then 1 else 0 := hd
  simp only [ggCZForm, hd', mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

theorem ggCZForm_e_apply {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (k : Fin m) (v : V) : ggCZForm φ (e k) v = φ k v := by
  rw [ggCZForm_comm, ggCZForm_apply_e hd]

@[expose] def GGCZGensB (e : Fin m → V) (φ : Fin m → Module.Dual (ZMod p) V)
    (r : V ≃ₗ[ZMod p] V) : Prop :=
  (∃ i j : Fin m, i.val + 1 = j.val ∧ ∀ v, r v = v - (φ i v - φ j v) • (e i - e j)) ∨
    ∃ i : Fin m, i.val + 1 = m ∧ ∀ v, r v = v - (2 * φ i v) • e i

variable (p) in
@[expose] noncomputable def ggCZWB (e : Fin m → V) (φ : Fin m → Module.Dual (ZMod p) V) :
    Subgroup (V ≃ₗ[ZMod p] V) :=
  Subgroup.closure {r | GGCZGensB e φ r}

theorem ggCZWB_fix {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V} {g : V ≃ₗ[ZMod p] V}
    (hg : g ∈ ggCZWB p e φ) {v : V} (hv : ∀ k, φ k v = 0) : g v = v := by
  induction hg using Subgroup.closure_induction with
  | mem r hr =>
    rcases hr with ⟨i, j, -, hr⟩ | ⟨i, -, hr⟩
    · rw [hr, hv i, hv j]; simp
    · rw [hr, hv i]; simp
  | one => rfl
  | mul g h _ _ hg hh => rw [LinearEquiv.mul_apply, hh, hg]
  | inv g _ hg =>
    change g.symm v = v
    rw [LinearEquiv.symm_apply_eq]
    exact hg.symm

@[expose] def GGCZGensF4 (e : Fin 4 → V) (φ : Fin 4 → Module.Dual (ZMod p) V) (i : Fin 4)
    (r : V ≃ₗ[ZMod p] V) : Prop :=
  match i with
  | 0 => ∀ v, r v = v - (φ 1 v - φ 2 v) • (e 1 - e 2)
  | 1 => ∀ v, r v = v - (φ 2 v - φ 3 v) • (e 2 - e 3)
  | 2 => ∀ v, r v = v - (2 * φ 3 v) • e 3
  | 3 => ∀ v, r v = v - ((2 : ZMod p)⁻¹ * (φ 0 v - φ 1 v - φ 2 v - φ 3 v)) •
      (e 0 - e 1 - e 2 - e 3)

variable (p) in
@[expose] noncomputable def ggCZWF4 (e : Fin 4 → V) (φ : Fin 4 → Module.Dual (ZMod p) V) :
    Subgroup (V ≃ₗ[ZMod p] V) :=
  Subgroup.closure {r | ∃ i, GGCZGensF4 e φ i r}

theorem ggCZWF4_fix {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V} {g : V ≃ₗ[ZMod p] V}
    (hg : g ∈ ggCZWF4 p e φ) {v : V} (hv : ∀ k, φ k v = 0) : g v = v := by
  induction hg using Subgroup.closure_induction with
  | mem r hr =>
    obtain ⟨i, hi⟩ := hr
    fin_cases i <;> simp only [GGCZGensF4] at hi <;> simp [hi, hv]
  | one => rfl
  | mul g h _ _ hg hh => rw [LinearEquiv.mul_apply, hh, hg]
  | inv g _ hg =>
    change g.symm v = v
    rw [LinearEquiv.symm_apply_eq]
    exact hg.symm

end

end CFSG.StandardType

end

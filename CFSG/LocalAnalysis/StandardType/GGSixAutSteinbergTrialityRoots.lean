module

public import CFSG.LieType.Steinberg.Classical.SpinPlus
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType

namespace Triality

open CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem CFSG.LieType.Steinberg.SpinFrame

@[expose] def tri : (Fin 4 → ℤ) →+ (Fin 4 → ℤ) where
  toFun v := ![v 3 - v 1, 2 * v 3 - v 1, v 2 + v 3 - v 1, v 3 - v 0]
  map_zero' := by
    funext a
    fin_cases a <;> simp
  map_add' v w := by
    funext a
    fin_cases a <;> simp <;> ring

theorem tri_apply (v : Fin 4 → ℤ) :
    tri v = ![v 3 - v 1, 2 * v 3 - v 1, v 2 + v 3 - v 1, v 3 - v 0] := rfl

@[expose] def refl0 : (Fin 4 → ℤ) →+ (Fin 4 → ℤ) where
  toFun v := ![-v 0, v 1 - 2 * v 0, v 2 - v 0, v 3 - v 0]
  map_zero' := by
    funext a
    fin_cases a <;> simp
  map_add' v w := by
    funext a
    fin_cases a <;> simp <;> ring

theorem refl0_apply (v : Fin 4 → ℤ) :
    refl0 v = ![-v 0, v 1 - 2 * v 0, v 2 - v 0, v 3 - v 0] := rfl

theorem tri_tri_tri (v : Fin 4 → ℤ) : tri (tri (tri v)) = v := by
  funext a
  fin_cases a <;> simp [tri_apply] <;> ring

theorem refl0_tri_refl0_tri (v : Fin 4 → ℤ) : refl0 (tri (refl0 (tri v))) = v := by
  funext a
  fin_cases a <;> simp [tri_apply, refl0_apply] <;> ring

theorem refl0_refl0 (v : Fin 4 → ℤ) : refl0 (refl0 v) = v := by
  funext a
  fin_cases a <;> simp [refl0_apply]

theorem tri_injective : Function.Injective tri := fun v w h => by
  rw [← tri_tri_tri v, ← tri_tri_tri w, h]

theorem refl0_injective : Function.Injective refl0 := fun v w h => by
  rw [← refl0_refl0 v, ← refl0_refl0 w, h]

theorem toStdD_refl0 (v : Fin 4 → ℤ) :
    toStdD 4 (refl0 v) = fun a => if a = 0 then -toStdD 4 v a else toStdD 4 v a := by
  funext a
  fin_cases a <;> simp [toStdD, refl0_apply] <;> ring

@[expose] def fromStd (e : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![e 0, e 0 + e 1, (e 0 + e 1 + e 2 - e 3) / 2, (e 0 + e 1 + e 2 + e 3) / 2]

abbrev lv (i j : Fin 4) (s t : Bool) : Fin 4 → ℤ :=
  Pi.single i (boolSign s) + Pi.single j (boolSign t)

theorem roots_check : ∀ i j : Fin 4, ∀ s t : Bool, i ≠ j →
    toStdD 4 (fromStd (lv i j s t)) = lv i j s t ∧
    (∃ i' j' : Fin 4, ∃ s' t' : Bool, i' ≠ j' ∧
      toStdD 4 (tri (fromStd (lv i j s t))) = lv i' j' s' t') ∧
    (∃ i' j' : Fin 4, ∃ s' t' : Bool, i' ≠ j' ∧
      toStdD 4 (refl0 (fromStd (lv i j s t))) = lv i' j' s' t') := by
  decide

abbrev rootsD4 : Set (Fin 4 → ℤ) := roots (isFiniteType_cartanD 4) ∅

theorem mem_rootsD4_iff {γ : Fin 4 → ℤ} : γ ∈ rootsD4 ↔ IsLong (toStdD 4 γ) :=
  (CFSG.LieType.Steinberg.SpinPlus.isLong_toStdD_iff (by norm_num)).symm

theorem exists_eq_fromStd {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) :
    ∃ (i j : Fin 4) (s t : Bool), i ≠ j ∧ toStdD 4 γ = lv i j s t ∧ γ = fromStd (lv i j s t) := by
  obtain ⟨i, j, hij, s, t, h⟩ := mem_rootsD4_iff.1 hγ
  exact ⟨i, j, s, t, hij, h, toStdD_injective 4 (h.trans (roots_check i j s t hij).1.symm)⟩

theorem tri_mem_roots {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) : tri γ ∈ rootsD4 := by
  obtain ⟨i, j, s, t, hij, -, rfl⟩ := exists_eq_fromStd hγ
  obtain ⟨-, ⟨i', j', s', t', hij', h⟩, -⟩ := roots_check i j s t hij
  exact mem_rootsD4_iff.2 ⟨i', j', hij', s', t', h⟩

theorem refl0_mem_roots {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) : refl0 γ ∈ rootsD4 := by
  obtain ⟨i, j, s, t, hij, -, rfl⟩ := exists_eq_fromStd hγ
  obtain ⟨-, -, ⟨i', j', s', t', hij', h⟩⟩ := roots_check i j s t hij
  exact mem_rootsD4_iff.2 ⟨i', j', hij', s', t', h⟩

theorem tri_mem_roots_iff {γ : Fin 4 → ℤ} : tri γ ∈ rootsD4 ↔ γ ∈ rootsD4 :=
  ⟨fun h => by
    rw [← tri_tri_tri γ]
    exact tri_mem_roots (tri_mem_roots h), tri_mem_roots⟩

theorem refl0_mem_roots_iff {γ : Fin 4 → ℤ} : refl0 γ ∈ rootsD4 ↔ γ ∈ rootsD4 :=
  ⟨fun h => by
    rw [← refl0_refl0 γ]
    exact refl0_mem_roots h, refl0_mem_roots⟩

@[expose] def flip0 (i : Fin 4) (s : Bool) : Bool := if i = 0 then !s else s

theorem flip0_check : ∀ i j : Fin 4, ∀ s t : Bool, i ≠ j →
    (fun a => if a = 0 then -lv i j s t a else lv i j s t a) =
      lv i j (flip0 i s) (flip0 j t) := by
  decide

theorem toStdD_refl0_of_eq {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 γ = lv i j s t) : toStdD 4 (refl0 γ) = lv i j (flip0 i s) (flip0 j t) := by
  rw [toStdD_refl0, h]
  exact flip0_check i j s t hij

@[expose] def rootC : Fin 4 → ℤ := ![-1, -1, -1, 0]

@[expose] def rootD : Fin 4 → ℤ := ![1, 1, 0, 1]

@[expose] def rootA : Fin 4 → ℤ := ![0, 1, 0, 0]

theorem toStdD_rootC : toStdD 4 rootC = lv 0 3 false true := by decide

theorem toStdD_rootD : toStdD 4 rootD = lv 0 3 true true := by decide

theorem toStdD_rootA : toStdD 4 rootA = lv 1 2 true false := by decide

theorem tri_rootC : tri rootC = rootD := by decide

theorem tri_rootD : tri rootD = rootA := by decide

theorem rootC_mem : rootC ∈ rootsD4 :=
  mem_rootsD4_iff.2 ⟨0, 3, by decide, false, true, toStdD_rootC⟩

theorem rootD_mem : rootD ∈ rootsD4 :=
  mem_rootsD4_iff.2 ⟨0, 3, by decide, true, true, toStdD_rootD⟩

theorem rootA_mem : rootA ∈ rootsD4 :=
  mem_rootsD4_iff.2 ⟨1, 2, by decide, true, false, toStdD_rootA⟩

end Triality

end CFSG.StandardType

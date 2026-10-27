module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Fintype.Card

import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Subgroup

section Lines

variable {X : Type*} [Group X]

theorem mem_zpowers_cases {a : X} (ha : a ^ 3 = 1) {b : X} (hb : b ∈ zpowers a) :
    b = 1 ∨ b = a ∨ b = a⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
  have h3 : a ^ (3 : ℤ) = 1 := by simpa using ha
  rw [zpow_eq_zpow_emod k h3]
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h | h | h <;> rw [h]
  · simp
  · simp
  · right; right
    have : a ^ (2 : ℤ) * a = 1 := by
      rw [← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num]
      exact h3
    exact eq_inv_of_mul_eq_one_left this

theorem conj_mem_zpowers_of_conj_mem {a b n : X} (h : n * a * n⁻¹ ∈ zpowers b) {z : X}
    (hz : z ∈ zpowers a) : n * z * n⁻¹ ∈ zpowers b := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
  have : n * a ^ k * n⁻¹ = (n * a * n⁻¹) ^ k := conj_zpow.symm
  rw [this]
  exact zpow_mem h k

@[expose] def LinePerm (a : Fin 3 → X) (n : X) (σ : Perm (Fin 3)) : Prop :=
  ∀ i, n * a i * n⁻¹ ∈ zpowers (a (σ i))

structure LineData (a : Fin 3 → X) : Prop where
  pow_three : ∀ i, a i ^ 3 = 1
  ne_one : ∀ i, a i ≠ 1
  not_mem : ∀ i j, j ≠ i → a j ∉ zpowers (a i)

namespace LinePerm

variable {a : Fin 3 → X}

theorem one : LinePerm a 1 1 := fun i => by simp

theorem mul {n m : X} {σ τ : Perm (Fin 3)} (hn : LinePerm a n σ) (hm : LinePerm a m τ) :
    LinePerm a (n * m) (σ * τ) := by
  intro i
  have h := conj_mem_zpowers_of_conj_mem (hn (τ i)) (hm i)
  rw [show n * m * a i * (n * m)⁻¹ = n * (m * a i * m⁻¹) * n⁻¹ by group]
  exact h

end LinePerm

namespace LineData

variable {a : Fin 3 → X}

theorem cases (hd : LineData a) (i : Fin 3) {b : X} (hb : b ∈ zpowers (a i)) :
    b = 1 ∨ b = a i ∨ b = (a i)⁻¹ := mem_zpowers_cases (hd.pow_three i) hb

theorem eq_of_mem (hd : LineData a) {i j : Fin 3} {b : X} (hb : b ≠ 1) (hbi : b ∈ zpowers (a i))
    (hbj : b ∈ zpowers (a j)) : i = j := by
  by_contra hij
  rcases hd.cases i hbi with h | h | h
  · exact hb h
  · rw [h] at hbj
    exact hd.not_mem j i hij hbj
  · rw [h] at hbj
    exact hd.not_mem j i hij (by simpa using inv_mem hbj)

theorem linePerm_unique (hd : LineData a) {n : X} {σ τ : Perm (Fin 3)} (hσ : LinePerm a n σ)
    (hτ : LinePerm a n τ) : σ = τ := by
  ext i
  have hne : n * a i * n⁻¹ ≠ 1 := by
    intro h
    apply hd.ne_one i
    calc a i = n⁻¹ * (n * a i * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  exact congrArg Fin.val (hd.eq_of_mem hne (hσ i) (hτ i))

theorem conj_ne_one (hd : LineData a) (n : X) (i : Fin 3) : n * a i * n⁻¹ ≠ 1 := fun h1 =>
  hd.ne_one i (by
    calc a i = n⁻¹ * (n * a i * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group)

theorem eq_of_mem_zpowers (hd : LineData a) {i i' : Fin 3} (h : a i' ∈ zpowers (a i)) : i' = i := by
  by_contra hne
  exact hd.not_mem i i' hne h

theorem exists_linePerm (hd : LineData a) {n : X}
    (h : ∀ i, ∃ j, n * a i * n⁻¹ ∈ zpowers (a j)) : ∃ σ : Perm (Fin 3), LinePerm a n σ := by
  choose f hf using h
  have hne : ∀ i, n * a i * n⁻¹ ≠ 1 := fun i h1 => hd.ne_one i (by
    calc a i = n⁻¹ * (n * a i * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group)
  have hinj : Function.Injective f := by
    intro i i' hii
    have h1 := hf i
    have h2 := hf i'
    rw [← hii] at h2
    have hb : a i' ∈ zpowers (a i) := by
      have conj_inj : ∀ u v : X, n * u * n⁻¹ = n * v * n⁻¹ → u = v := fun u v e => by
        have := congrArg (fun z => n⁻¹ * z * n) e
        simpa [mul_assoc] using this
      rcases hd.cases (f i) h1 with e1 | e1 | e1
      · exact absurd e1 (hne i)
      · rcases hd.cases (f i) h2 with e2 | e2 | e2
        · exact absurd e2 (hne i')
        · have : a i' = a i := conj_inj _ _ (e2.trans e1.symm)
          rw [this]; exact mem_zpowers _
        · have : a i' = (a i)⁻¹ := conj_inj (a i') (a i)⁻¹ (by
            rw [e2]; rw [show n * (a i)⁻¹ * n⁻¹ = (n * a i * n⁻¹)⁻¹ by group, e1])
          rw [this]; exact inv_mem (mem_zpowers _)
      · rcases hd.cases (f i) h2 with e2 | e2 | e2
        · exact absurd e2 (hne i')
        · have : a i' = (a i)⁻¹ := conj_inj (a i') (a i)⁻¹ (by
            rw [e2]; rw [show n * (a i)⁻¹ * n⁻¹ = (n * a i * n⁻¹)⁻¹ by group, e1]; simp)
          rw [this]; exact inv_mem (mem_zpowers _)
        · have : a i' = a i := conj_inj _ _ (e2.trans e1.symm)
          rw [this]; exact mem_zpowers _
    exact (hd.eq_of_mem_zpowers hb).symm
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩

theorem linePerm_inv (hd : LineData a) {n : X} {σ : Perm (Fin 3)} (hσ : LinePerm a n σ) :
    LinePerm a n⁻¹ σ⁻¹ := by
  intro i
  set j := σ⁻¹ i with hj
  have hij : σ j = i := by simp [hj]
  have h1 : n * a j * n⁻¹ ∈ zpowers (a i) := by simpa [hij] using hσ j
  have hne : n * a j * n⁻¹ ≠ 1 := by
    intro h
    apply hd.ne_one j
    calc a j = n⁻¹ * (n * a j * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  have key : n⁻¹ * a i * n ∈ zpowers (a j) := by
    rcases hd.cases i h1 with h | h | h
    · exact absurd h hne
    · have : n⁻¹ * a i * n = a j := by
        rw [← h]; group
      rw [this]; exact mem_zpowers _
    · have : n⁻¹ * a i * n = (a j)⁻¹ := by
        have : a i = (n * a j * n⁻¹)⁻¹ := by rw [h]; simp
        rw [this]; group
      rw [this]; exact inv_mem (mem_zpowers _)
  simpa using key

end LineData

@[expose] def permutingLines (a : Fin 3 → X) (hd : LineData a) : Subgroup X where
  carrier := {n | ∃ σ, LinePerm a n σ}
  mul_mem' := by
    rintro _ _ ⟨σ, hσ⟩ ⟨τ, hτ⟩
    exact ⟨σ * τ, hσ.mul hτ⟩
  one_mem' := ⟨1, LinePerm.one⟩
  inv_mem' := by
    rintro _ ⟨σ, hσ⟩
    exact ⟨σ⁻¹, hd.linePerm_inv hσ⟩

theorem mem_permutingLines {a : Fin 3 → X} (hd : LineData a) {n : X} :
    n ∈ permutingLines a hd ↔ ∃ σ, LinePerm a n σ := Iff.rfl

@[expose] noncomputable def choosePerm (a : Fin 3 → X) (hd : LineData a)
    (n : ↥(permutingLines a hd)) : Perm (Fin 3) := Classical.choose n.2

theorem choosePerm_spec {a : Fin 3 → X} (hd : LineData a) (n : ↥(permutingLines a hd)) :
    LinePerm a (n : X) (choosePerm a hd n) := Classical.choose_spec n.2

@[expose] noncomputable def lineHom (a : Fin 3 → X) (hd : LineData a) :
    ↥(permutingLines a hd) →* Perm (Fin 3) where
  toFun := choosePerm a hd
  map_one' := hd.linePerm_unique (choosePerm_spec hd 1) LinePerm.one
  map_mul' n m := hd.linePerm_unique (choosePerm_spec hd (n * m))
    ((choosePerm_spec hd n).mul (choosePerm_spec hd m))

theorem lineHom_spec {a : Fin 3 → X} (hd : LineData a) (n : ↥(permutingLines a hd)) :
    LinePerm a (n : X) (lineHom a hd n) := choosePerm_spec hd n

theorem lineHom_eq_of_linePerm {a : Fin 3 → X} (hd : LineData a) (n : ↥(permutingLines a hd))
    {σ : Perm (Fin 3)} (h : LinePerm a (n : X) σ) : lineHom a hd n = σ :=
  hd.linePerm_unique (lineHom_spec hd n) h

theorem lineHom_eq_one_iff {a : Fin 3 → X} (hd : LineData a) (n : ↥(permutingLines a hd)) :
    lineHom a hd n = 1 ↔ ∀ i, (n : X) * a i * (n : X)⁻¹ ∈ zpowers (a i) := by
  constructor
  · intro h i
    have := lineHom_spec hd n i
    rwa [h, Equiv.Perm.one_apply] at this
  · intro h
    exact lineHom_eq_of_linePerm hd n (σ := 1) (fun i => by simpa using h i)

end Lines

end CFSG.Sporadic.Recognition.LyonsSims

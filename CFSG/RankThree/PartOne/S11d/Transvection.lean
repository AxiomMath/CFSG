module

import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.RankThree.PartOne.Transv

open Subgroup

variable {G : Type*} [Group G]

@[expose] def lam (g e : G) : G := g * e * g⁻¹ * e⁻¹

theorem lam_mul (g h e : G) : lam (g * h) e = g * lam h e * g⁻¹ * lam g e := by
  simp only [lam]
  group

structure IsTransv (A : Subgroup G) (d g : G) : Prop where
  norm : g ∈ normalizer (A : Set G)
  cent : g * d = d * g
  comm : ∀ e ∈ A, lam g e ∈ zpowers d

variable {A : Subgroup G} {d : G}

theorem comm_of_mem_zpowers {g x : G} (hg : g * d = d * g) (hx : x ∈ zpowers d) :
    g * x = x * g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  exact (Commute.zpow_right (show Commute g d from hg) k).eq


theorem comm_of_zpowers {x y : G} (hx : x ∈ zpowers (d : G)) (hy : y ∈ zpowers d) :
    x * y = y * x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hy
  exact (Commute.zpow_zpow_self d k l).eq

theorem lam_mul_eq {g h : G} (hg : IsTransv A d g) (hh : IsTransv A d h) {e : G} (he : e ∈ A) :
    lam (g * h) e = lam h e * lam g e := by
  rw [lam_mul]
  have h1 := comm_of_mem_zpowers hg.cent (hh.comm e he)
  have : g * lam h e * g⁻¹ = lam h e := by
    rw [h1]
    group
  rw [this]

theorem IsTransv.one (A : Subgroup G) (d : G) : IsTransv A d 1 where
  norm := Subgroup.one_mem _
  cent := by simp
  comm e _ := by simp [lam]

theorem IsTransv.mul {g h : G} (hg : IsTransv A d g) (hh : IsTransv A d h) :
    IsTransv A d (g * h) where
  norm := Subgroup.mul_mem _ hg.norm hh.norm
  cent := by
    calc g * h * d = g * (h * d) := by rw [mul_assoc]
      _ = g * (d * h) := by rw [hh.cent]
      _ = (g * d) * h := by rw [mul_assoc]
      _ = (d * g) * h := by rw [hg.cent]
      _ = d * (g * h) := by rw [mul_assoc]
  comm e he := by
    rw [lam_mul_eq hg hh he]
    exact Subgroup.mul_mem _ (hh.comm e he) (hg.comm e he)

theorem IsTransv.inv {g : G} (hg : IsTransv A d g) : IsTransv A d g⁻¹ where
  norm := Subgroup.inv_mem _ hg.norm
  cent := by
    have h1 : g⁻¹ * (g * d) * g⁻¹ = g⁻¹ * (d * g) * g⁻¹ := by rw [hg.cent]
    simpa [mul_assoc] using h1.symm
  comm e he := by
    have he' : g⁻¹ * e * g ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg.norm) e).mp he
      simpa using this
    have h1 := hg.comm (g⁻¹ * e * g) he'
    have h2 : lam g (g⁻¹ * e * g) = e * (g⁻¹ * e * g)⁻¹ := by
      simp only [lam]
      group
    rw [h2] at h1
    have h3 : lam g⁻¹ e = (e * (g⁻¹ * e * g)⁻¹)⁻¹ := by
      simp only [lam]
      group
    rw [h3]
    exact Subgroup.inv_mem _ h1

@[expose] def transvGroup (A : Subgroup G) (d : G) : Subgroup G where
  carrier := {g | IsTransv A d g}
  mul_mem' := fun hg hh => hg.mul hh
  one_mem' := IsTransv.one A d
  inv_mem' := fun hg => hg.inv

theorem mem_transvGroup {g : G} : g ∈ transvGroup A d ↔ IsTransv A d g := Iff.rfl


theorem lam_inv_eq {g : G} (hg : IsTransv A d g) {e : G} (he : e ∈ A) :
    lam g⁻¹ e = (lam g e)⁻¹ := by
  have h := lam_mul_eq hg hg.inv he
  have h1 : lam (g * g⁻¹) e = 1 := by simp [lam]
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem lam_one (e : G) : lam (1 : G) e = 1 := by simp [lam]

theorem lam_zpow {g : G} (hg : IsTransv A d g) {e : G} (he : e ∈ A) (k : ℤ) :
    lam (g ^ k) e = (lam g e) ^ k := by
  have hnat : ∀ n : ℕ, lam (g ^ n) e = (lam g e) ^ n := by
    intro n
    induction n with
    | zero => simp [lam_one]
    | succ n ih =>
      have hgn : IsTransv A d (g ^ n) := by
        have : g ^ n ∈ transvGroup A d := (transvGroup A d).pow_mem hg n
        exact this
      rw [pow_succ, lam_mul_eq hgn hg he, ih, pow_succ']
  rcases k with n | n
  · simpa using hnat n
  · have hgn : IsTransv A d (g ^ (n + 1)) := by
      have : g ^ (n + 1) ∈ transvGroup A d := (transvGroup A d).pow_mem hg (n + 1)
      exact this
    rw [zpow_negSucc, zpow_negSucc, lam_inv_eq hgn he, hnat]

theorem lam_mul_right (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hdA : d ∈ A) {g : G}
    (hg : IsTransv A d g) {e e' : G} (he : e ∈ A) (he' : e' ∈ A) :
    lam g (e * e') = lam g e * lam g e' := by
  have h1 : lam g e' ∈ A := (zpowers_le.mpr hdA) (hg.comm e' he')
  have h2 : e * lam g e' = lam g e' * e := hA e he _ h1
  have h3 : lam g (e * e') = lam g e * (e * lam g e' * e⁻¹) := by
    simp only [lam]
    group
  rw [h3, h2]
  simp

theorem mem_centralizer_iff_lam_eq_one {g : G} :
    g ∈ centralizer (A : Set G) ↔ ∀ e ∈ A, lam g e = 1 := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h e he
    have := h e he
    simp only [lam]
    rw [mul_assoc, ← this]
    group
  · intro h e he
    have := h e he
    simp only [lam] at this
    have h2 : g * e * g⁻¹ = e := by
      have := congrArg (fun z => z * e) this
      simpa [mul_assoc] using this
    calc e * g = (g * e * g⁻¹) * g := by rw [h2]
      _ = g * e := by group

theorem commutator_mem_centralizer {g h : G} (hg : IsTransv A d g) (hh : IsTransv A d h) :
    g * h * g⁻¹ * h⁻¹ ∈ centralizer (A : Set G) := by
  rw [mem_centralizer_iff_lam_eq_one]
  intro e₂ he₂
  have hhg : IsTransv A d (h * g) := hh.mul hg
  set e : G := (h * g)⁻¹ * e₂ * (h * g) with hedef
  have heA : e ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhg.norm) e₂).mp he₂
    simpa [hedef] using this
  have hcomm : lam (g * h) e = lam (h * g) e := by
    rw [lam_mul_eq hg hh heA, lam_mul_eq hh hg heA]
    exact comm_of_zpowers (hh.comm e heA) (hg.comm e heA)
  have he₂' : e₂ = (h * g) * e * (h * g)⁻¹ := by
    simp [hedef, mul_assoc]
  have h1 : (g * h) * e * (g * h)⁻¹ = (h * g) * e * (h * g)⁻¹ := by
    have := hcomm
    simp only [lam] at this
    have h2 := congrArg (fun z => z * e) this
    simpa [mul_assoc] using h2
  simp only [lam]
  calc (g * h * g⁻¹ * h⁻¹) * e₂ * (g * h * g⁻¹ * h⁻¹)⁻¹ * e₂⁻¹
      = ((g * h) * ((h * g)⁻¹ * ((h * g) * e * (h * g)⁻¹) * (h * g)) * (g * h)⁻¹)
        * ((h * g) * e * (h * g)⁻¹)⁻¹ := by rw [← he₂']; group
    _ = 1 := by
      have h3 : (g * h) * e * (g * h)⁻¹ = (h * g) * e * (h * g)⁻¹ := h1
      calc _ = ((g * h) * e * (g * h)⁻¹) * ((h * g) * e * (h * g)⁻¹)⁻¹ := by group
        _ = 1 := by rw [h3]; group

theorem pow_mem_centralizer {p : ℕ} (hdp : d ^ p = 1) {g : G} (hg : IsTransv A d g) :
    g ^ p ∈ centralizer (A : Set G) := by
  rw [mem_centralizer_iff_lam_eq_one]
  intro e he
  rw [← zpow_natCast, lam_zpow hg he]
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg.comm e he)
  rw [← hk, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdp, one_zpow]

theorem lam_conj {g h : G} (hg : IsTransv A d g) (hh : IsTransv A d h) {e : G} (he : e ∈ A) :
    lam (h * g * h⁻¹) e = lam g e := by
  have hhg : IsTransv A d (h * g) := hh.mul hg
  rw [lam_mul_eq hhg hh.inv he, lam_mul_eq hh hg he, lam_inv_eq hh he]
  rw [comm_of_zpowers (hg.comm e he) (hh.comm e he), inv_mul_cancel_left]

theorem lam_zpow_right (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hdA : d ∈ A) {g : G}
    (hg : IsTransv A d g) {e : G} (he : e ∈ A) (k : ℤ) : lam g (e ^ k) = (lam g e) ^ k := by
  have hnat : ∀ n : ℕ, lam g (e ^ n) = (lam g e) ^ n := by
    intro n
    induction n with
    | zero => simp [lam]
    | succ n ih =>
      rw [pow_succ, lam_mul_right hA hdA hg (A.pow_mem he n) he, ih, pow_succ]
  rcases k with n | n
  · simpa using hnat n
  · have hen : e ^ (n + 1) ∈ A := A.pow_mem he (n + 1)
    have h1 : lam g ((e ^ (n + 1)) * (e ^ (n + 1))⁻¹) = 1 := by simp [lam]
    rw [lam_mul_right hA hdA hg hen (A.inv_mem hen), hnat] at h1
    rw [zpow_negSucc, zpow_negSucc]
    exact eq_inv_of_mul_eq_one_right h1

theorem commutator_inv_mem_zpowers (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hdA : d ∈ A) {g : G}
    (hg : IsTransv A d g) {β : G} (hβ : β ∈ A) : β⁻¹ * g⁻¹ * β * g ∈ zpowers d := by
  have h1 := hg.inv.comm β hβ
  have h2 : β⁻¹ * g⁻¹ * β * g = β⁻¹ * lam g⁻¹ β * β := by
    simp only [lam]
    group
  have h3 : β * lam g⁻¹ β = lam g⁻¹ β * β := hA β hβ _ ((zpowers_le.mpr hdA) h1)
  rw [h2]
  have h4 : β⁻¹ * lam g⁻¹ β * β = lam g⁻¹ β := by
    rw [mul_assoc, ← h3]
    group
  rw [h4]
  exact h1

end CFSG.RankThree.PartOne.Transv

module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise

import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE1

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_inf {X U W : Subgroup G} (hU : X ≤ normalizer (U : Set G))
    (hW : X ≤ normalizer (W : Set G)) : X ≤ normalizer ((U ⊓ W : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro y
  exact and_congr (mem_normalizer_iff.mp (hU hg) y) (mem_normalizer_iff.mp (hW hg) y)

theorem normalizer_le_normalizer_centralizer (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (centralizer (X : Set G) : Set G) := by
  have key : ∀ h ∈ normalizer (X : Set G), ∀ c ∈ centralizer (X : Set G),
      h * c * h⁻¹ ∈ centralizer (X : Set G) := by
    intro h hh c hc
    rw [mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : h⁻¹ * x * h ∈ X := by
      have := (mem_normalizer_iff.mp hh (h⁻¹ * x * h)).mpr
      exact this (by simpa [mul_assoc] using hx)
    have h1 := hc _ hx'
    calc x * (h * c * h⁻¹) = h * ((h⁻¹ * x * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * x * h)) * h⁻¹ := by rw [h1]
      _ = h * c * h⁻¹ * x := by group
  intro h hh
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key h hh c, fun hc => ?_⟩
  have := key h⁻¹ (inv_mem hh) _ hc
  have e : h⁻¹ * (h * c * h⁻¹) * h⁻¹⁻¹ = c := by group
  rwa [e] at this

theorem le_normalizer_of_le_comm {A U W : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hUA : U ≤ A) (hWA : W ≤ A) : U ≤ normalizer (W : Set G) := by
  intro u hu
  rw [mem_normalizer_iff]
  intro y
  have key : ∀ y ∈ A, u * y * u⁻¹ = y := fun y hy => by
    rw [hA u (hUA hu) y hy, mul_inv_cancel_right]
  constructor
  · intro hy
    rw [key y (hWA hy)]
    exact hy
  · intro hy
    have hyA : y ∈ A := by
      have h1 := A.mul_mem (A.mul_mem (A.inv_mem (hUA hu)) (hWA hy)) (hUA hu)
      have e : u⁻¹ * (u * y * u⁻¹) * u = y := by group
      rwa [e] at h1
    rwa [key y hyA] at hy

theorem mem_of_forall_commutator_mem {X W : Subgroup G}
    (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hXW : X ≤ normalizer (W : Set G))
    (hWX : ⁅W, X⁆ = W) (hlt : W ⊓ centralizer (X : Set G) < W)
    (hirr : ∀ J : Subgroup G, W ⊓ centralizer (X : Set G) ≤ J → J ≤ W →
      X ≤ normalizer (J : Set G) → J = W ⊓ centralizer (X : Set G) ∨ J = W)
    {w : G} (hw : w ∈ W) (hc : ∀ g ∈ X, ⁅w, g⁆ ∈ W ⊓ centralizer (X : Set G)) :
    w ∈ W ⊓ centralizer (X : Set G) := by
  set Z := W ⊓ centralizer (X : Set G) with hZ
  have hXZ : X ≤ normalizer (Z : Set G) :=
    le_normalizer_inf hXW (le_normalizer.trans (normalizer_le_normalizer_centralizer X))
  let F : Subgroup G :=
    { carrier := {y | y ∈ W ∧ ∀ g ∈ X, ⁅y, g⁆ ∈ Z}
      mul_mem' := by
        rintro a b ⟨ha, hag⟩ ⟨hb, hbg⟩
        refine ⟨W.mul_mem ha hb, fun g hg => ?_⟩
        have hcb := hbg g hg
        have hcomm : a * ⁅b, g⁆ = ⁅b, g⁆ * a := hWc a ha _ hcb.1
        have e : ⁅a * b, g⁆ = ⁅b, g⁆ * ⁅a, g⁆ := by
          calc ⁅a * b, g⁆ = a * ⁅b, g⁆ * (g * a⁻¹ * g⁻¹) := by
                simp only [commutatorElement_def]; group
            _ = ⁅b, g⁆ * a * (g * a⁻¹ * g⁻¹) := by rw [hcomm]
            _ = ⁅b, g⁆ * ⁅a, g⁆ := by simp only [commutatorElement_def]; group
        rw [e]
        exact Z.mul_mem hcb (hag g hg)
      one_mem' := ⟨W.one_mem, fun g _ => by
        rw [commutatorElement_def, one_mul, inv_one, mul_one, mul_inv_cancel]
        exact Z.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, hag⟩
        refine ⟨W.inv_mem ha, fun g hg => ?_⟩
        have hca := hag g hg
        have hcomm : a⁻¹ * ⁅a, g⁆⁻¹ = ⁅a, g⁆⁻¹ * a⁻¹ :=
          hWc _ (W.inv_mem ha) _ (W.inv_mem hca.1)
        have e : ⁅a⁻¹, g⁆ = ⁅a, g⁆⁻¹ := by
          calc ⁅a⁻¹, g⁆ = a⁻¹ * ⁅a, g⁆⁻¹ * a := by simp only [commutatorElement_def]; group
            _ = ⁅a, g⁆⁻¹ * a⁻¹ * a := by rw [hcomm]
            _ = ⁅a, g⁆⁻¹ := by group
        rw [e]
        exact Z.inv_mem hca }
  have hmemF : ∀ y, y ∈ F ↔ y ∈ W ∧ ∀ g ∈ X, ⁅y, g⁆ ∈ Z := fun y => Iff.rfl
  have hZF : Z ≤ F := fun z hz => (hmemF z).mpr ⟨hz.1, fun g hg => by
    have hgz : g * z = z * g := (mem_centralizer_iff.mp hz.2) g hg
    have e : ⁅z, g⁆ = 1 := by
      rw [commutatorElement_def, ← hgz]
      group
    rw [e]
    exact Z.one_mem⟩
  have hFW : F ≤ W := fun y hy => ((hmemF y).mp hy).1
  have key : ∀ h ∈ X, ∀ y ∈ F, h * y * h⁻¹ ∈ F := by
    intro h hh y hy
    obtain ⟨hyW, hyg⟩ := (hmemF y).mp hy
    refine (hmemF _).mpr ⟨(mem_normalizer_iff.mp (hXW hh) y).mp hyW, fun g hg => ?_⟩
    have hg' : h⁻¹ * g * h ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hh) hg) hh
    have e : ⁅h * y * h⁻¹, g⁆ = h * ⁅y, h⁻¹ * g * h⁆ * h⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (mem_normalizer_iff.mp (hXZ hh) _).mp (hyg _ hg')
  have hXF : X ≤ normalizer (F : Set G) := by
    intro h hh
    rw [mem_normalizer_iff]
    intro y
    refine ⟨key h hh y, fun hy => ?_⟩
    have := key h⁻¹ (X.inv_mem hh) _ hy
    have e : h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ = y := by group
    rwa [e] at this
  rcases hirr F hZF hFW hXF with hF | hF
  · have hwF : w ∈ F := (hmemF w).mpr ⟨hw, hc⟩
    rw [hF] at hwF
    exact hwF
  · exfalso
    have hle : ⁅W, X⁆ ≤ Z := commutator_le.mpr fun y hy g hg => by
      have hyF : y ∈ F := by rw [hF]; exact hy
      exact ((hmemF y).mp hyF).2 g hg
    rw [hWX] at hle
    exact lt_irrefl _ (lt_of_lt_of_le hlt hle)

theorem sup_inf_centralizer_le {X A U W C : Subgroup G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hUA : U ≤ A) (hWA : W ≤ A)
    (hXU : X ≤ normalizer (U : Set G)) (hXW : X ≤ normalizer (W : Set G))
    (hWX : ⁅W, X⁆ = W) (hlt : W ⊓ centralizer (X : Set G) < W)
    (hirr : ∀ J : Subgroup G, W ⊓ centralizer (X : Set G) ≤ J → J ≤ W →
      X ≤ normalizer (J : Set G) → J = W ⊓ centralizer (X : Set G) ∨ J = W)
    (hWC : W ⊓ centralizer (X : Set G) ≤ C) (hCU : C ≤ U)
    (hU : U ⊓ centralizer (X : Set G) ≤ C) :
    (U ⊔ W) ⊓ centralizer (X : Set G) ≤ C := by
  rintro x ⟨hxUW, hxC⟩
  have hmem : x ∈ ((U ⊔ W : Subgroup G) : Set G) := hxUW
  rw [coe_mul_of_left_le_normalizer_right U W (le_normalizer_of_le_comm hA hUA hWA)] at hmem
  obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.mp hmem
  have hcU : ∀ g ∈ X, ⁅w, g⁆ ∈ U ⊓ W := fun g hg => by
    have hx : g * (u * w) = u * w * g := (mem_centralizer_iff.mp hxC) g hg
    have e : ⁅w, g⁆ = u⁻¹ * (g * u * g⁻¹) := by
      calc ⁅w, g⁆ = u⁻¹ * (u * w * g) * w⁻¹ * g⁻¹ := by rw [commutatorElement_def]; group
        _ = u⁻¹ * (g * (u * w)) * w⁻¹ * g⁻¹ := by rw [hx]
        _ = u⁻¹ * (g * u * g⁻¹) := by group
    refine ⟨?_, ?_⟩
    · rw [e]
      exact U.mul_mem (U.inv_mem hu) ((mem_normalizer_iff.mp (hXU hg) u).mp hu)
    · have e' : ⁅w, g⁆ = w * (g * w⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
      rw [e']
      exact W.mul_mem hw ((mem_normalizer_iff.mp (hXW hg) _).mp (W.inv_mem hw))
  have hD1 : W ⊓ centralizer (X : Set G) ≤ U ⊓ W := le_inf (hWC.trans hCU) inf_le_left
  rcases hirr (U ⊓ W) hD1 inf_le_right (le_normalizer_inf hXU hXW) with hD | hD
  ·
    have hwZ : w ∈ W ⊓ centralizer (X : Set G) :=
      mem_of_forall_commutator_mem (fun a ha b hb => hA a (hWA ha) b (hWA hb)) hXW hWX hlt
        hirr hw (fun g hg => by rw [← hD]; exact hcU g hg)
    have huC : u ∈ U ⊓ centralizer (X : Set G) := by
      refine ⟨hu, ?_⟩
      have e : u = u * w * w⁻¹ := by group
      rw [e]
      exact (centralizer _).mul_mem hxC ((centralizer _).inv_mem hwZ.2)
    exact C.mul_mem (hU huC) (hWC hwZ)
  ·
    have hWU : W ≤ U := inf_eq_right.mp hD
    exact hU ⟨U.mul_mem hu (hWU hw), hxC⟩

end CFSG.Quasithin.Vol2.Ch11.OE1

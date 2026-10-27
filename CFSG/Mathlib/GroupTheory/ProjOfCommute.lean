module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.Group
public import CFSG.Mathlib.GroupTheory.SubgroupSupCommute

public section

namespace CFSG.GroupTheory

theorem exists_proj_of_le_sup_of_commute {X : Type} [Group X] {H Y R : Subgroup X}
    (hYH : Y ≤ H) (hH : H ≤ Y ⊔ R) (hc : ∀ y ∈ Y, ∀ r ∈ R, y * r = r * y) (hYR : Y ⊓ R = ⊥) :
    ∃ p : ↥H →* ↥Y, Function.Surjective p ∧ p.ker = R.subgroupOf H ∧
      ∀ h : ↥H, (h : X) ∈ Y → (p h : X) = h := by
  classical
  have hex : ∀ h : H, ∃ y : Y, ∃ r : R, (h : X) = (y : X) * (r : X) := by
    intro h
    obtain ⟨y, hy, r, hr, hEq⟩ :=
      (Subgroup.mem_sup_iff_of_forall_commute (H := Y) (K := R) hc).mp (hH h.2)
    exact ⟨⟨y, hy⟩, ⟨r, hr⟩, hEq⟩
  have huniq : ∀ {y₁ y₂ : Y} {r₁ r₂ : R},
      (y₁ : X) * (r₁ : X) = (y₂ : X) * (r₂ : X) → y₁ = y₂ := by
    intro y₁ y₂ r₁ r₂ hEq
    have hconj : (y₂ : X)⁻¹ * (y₁ : X) = (r₂ : X) * (r₁ : X)⁻¹ := by
      calc (y₂ : X)⁻¹ * (y₁ : X)
          = (y₂ : X)⁻¹ * ((y₁ : X) * (r₁ : X)) * (r₁ : X)⁻¹ := by group
        _ = (y₂ : X)⁻¹ * ((y₂ : X) * (r₂ : X)) * (r₁ : X)⁻¹ := by rw [hEq]
        _ = (r₂ : X) * (r₁ : X)⁻¹ := by group
    have hmem : ((y₂ : X)⁻¹ * (y₁ : X)) ∈ Y ⊓ R := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Y.mul_mem (Y.inv_mem y₂.2) y₁.2
      · rw [hconj]
        exact R.mul_mem r₂.2 (R.inv_mem r₁.2)
    have hbot : ((y₂ : X)⁻¹ * (y₁ : X)) ∈ (⊥ : Subgroup X) := by
      rw [← hYR]
      exact hmem
    have h1 : (y₂ : X)⁻¹ * (y₁ : X) = 1 := Subgroup.mem_bot.mp hbot
    exact Subtype.ext ((inv_mul_eq_one.mp h1).symm)
  let projFun : H → Y := fun h => (hex h).choose
  have projFun_spec : ∀ h : H, ∃ r : R, (h : X) = (projFun h : X) * (r : X) :=
    fun h => (hex h).choose_spec
  have projFun_unique : ∀ {h : H} {y : Y} {r : R},
      (h : X) = (y : X) * (r : X) → projFun h = y := by
    intro h y r hEq
    obtain ⟨r', hr'⟩ := projFun_spec h
    exact huniq (by rw [← hr', hEq])
  have projFun_mul : ∀ a b : H, projFun (a * b) = projFun a * projFun b := by
    intro a b
    obtain ⟨ra, hra⟩ := projFun_spec a
    obtain ⟨rb, hrb⟩ := projFun_spec b
    have hcomm : (ra : X) * (projFun b : X) = (projFun b : X) * (ra : X) :=
      (hc (projFun b) (projFun b).2 ra ra.2).symm
    refine projFun_unique (r := ra * rb) ?_
    change (a : X) * (b : X) =
      ((projFun a : X) * (projFun b : X)) * ((ra : X) * (rb : X))
    rw [hra, hrb]
    calc ((projFun a : X) * (ra : X)) * ((projFun b : X) * (rb : X))
        = (projFun a : X) * (((ra : X) * (projFun b : X)) * (rb : X)) := by group
      _ = (projFun a : X) * (((projFun b : X) * (ra : X)) * (rb : X)) := by rw [hcomm]
      _ = ((projFun a : X) * (projFun b : X)) * ((ra : X) * (rb : X)) := by group
  have projFun_one : projFun 1 = 1 := by
    refine projFun_unique (y := 1) (r := 1) ?_
    simp
  let proj : ↥H →* ↥Y :=
    { toFun := projFun
      map_one' := projFun_one
      map_mul' := projFun_mul }
  have proj_surj : Function.Surjective proj := by
    intro y
    refine ⟨⟨(y : X), hYH y.2⟩, ?_⟩
    change projFun ⟨(y : X), hYH y.2⟩ = y
    refine projFun_unique (r := 1) ?_
    simp
  have proj_ker : proj.ker = R.subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : projFun x = 1 := hx
      obtain ⟨r, hr⟩ := projFun_spec x
      have hxr : (x : X) = (r : X) := by
        rw [hr, hx']
        simp
      rw [hxr]
      exact r.2
    · intro hx
      have hx' : projFun x = 1 := by
        refine projFun_unique (y := 1) (r := ⟨(x : X), hx⟩) ?_
        simp
      change projFun x = 1
      exact hx'
  refine ⟨proj, proj_surj, proj_ker, ?_⟩
  intro h hy
  have h' : projFun h = ⟨(h : X), hy⟩ := by
    refine projFun_unique (r := 1) ?_
    simp
  calc (proj h : X) = (projFun h : X) := rfl
    _ = (h : X) := by rw [h']

end CFSG.GroupTheory

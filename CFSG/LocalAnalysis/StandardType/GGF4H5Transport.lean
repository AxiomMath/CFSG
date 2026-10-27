module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import Mathlib.GroupTheory.Coxeter.Inversion

public section

namespace CFSG.StandardType

open CFSG

theorem ggF4H5Pos_A3_transport {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {A AL : Subgroup (MulAut ↥Bs)} (e : CoxeterMatrix.F₄.Group ≃* ↥A)
    (hAL : AL ≤ A) (hA : GGWeylOfType p (CoxeterMatrix.A 3) AL)
    (hconv : ∀ w : CoxeterMatrix.F₄.Group,
      GGIsReflection p ((e w : ↥A) : MulAut ↥Bs) →
        (CoxeterMatrix.F₄.toCoxeterSystem).IsReflection w) :
    ∃ a : Fin 3 → CoxeterMatrix.F₄.Group,
      (∀ j, (CoxeterMatrix.F₄.toCoxeterSystem).IsReflection (a j)) ∧
      orderOf (a 0 * a 1) = 3 ∧ orderOf (a 1 * a 2) = 3 ∧
      orderOf (a 0 * a 2) = 2 ∧
      ∀ w : CoxeterMatrix.F₄.Group,
        ((e w : ↥A) : MulAut ↥Bs) ∈ AL ↔ w ∈ Subgroup.closure (Set.range a) := by
  obtain ⟨eAL, hreflAL⟩ := hA
  let fA : (CoxeterMatrix.A 3).Group →* CoxeterMatrix.F₄.Group :=
    (e.symm : ↥A →* CoxeterMatrix.F₄.Group).comp
      ((Subgroup.inclusion hAL).comp (eAL : (CoxeterMatrix.A 3).Group →* ↥AL))
  let a : Fin 3 → CoxeterMatrix.F₄.Group :=
    fun j => fA ((CoxeterMatrix.A 3).simple j)
  have hfA_inj : Function.Injective fA := by
    intro x y hxy
    have h1 : Subgroup.inclusion hAL (eAL x) = Subgroup.inclusion hAL (eAL y) := by
      have h2 := congrArg e hxy
      simpa [fA] using h2
    exact eAL.injective (Subgroup.inclusion_injective hAL h1)
  have ha_refl : ∀ j, (CoxeterMatrix.F₄.toCoxeterSystem).IsReflection (a j) := by
    intro j
    refine hconv (a j) ?_
    have hx : e (a j) =
        Subgroup.inclusion hAL (eAL ((CoxeterMatrix.A 3).simple j)) := by
      simp [a, fA]
    rw [hx]
    simpa using hreflAL j
  have hmem_fA : ∀ w : CoxeterMatrix.F₄.Group,
      w ∈ fA.range ↔ ((e w : ↥A) : MulAut ↥Bs) ∈ AL := by
    intro w
    constructor
    · rintro ⟨x, rfl⟩
      have hx : e (fA x) = Subgroup.inclusion hAL (eAL x) := by simp [fA]
      rw [hx]
      exact (eAL x).2
    · intro hw
      let x : (CoxeterMatrix.A 3).Group :=
        eAL.symm ⟨((e w : ↥A) : MulAut ↥Bs), hw⟩
      refine ⟨x, ?_⟩
      apply e.injective
      have hx : eAL x = ⟨((e w : ↥A) : MulAut ↥Bs), hw⟩ := eAL.apply_symm_apply _
      have h1 : e (fA x) = Subgroup.inclusion hAL (eAL x) := by simp [fA]
      rw [h1, hx]
      exact Subtype.ext rfl
  have hgenA : Subgroup.closure
      (Set.range (fun j : Fin 3 => (CoxeterMatrix.A 3).simple j)) = ⊤ :=
    (CoxeterMatrix.A 3).toCoxeterSystem.subgroup_closure_range_simple
  have ha_range : Set.range a =
      fA '' Set.range (fun j : Fin 3 => (CoxeterMatrix.A 3).simple j) := by
    ext w
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨(CoxeterMatrix.A 3).simple j, ⟨j, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
  have hclosure : Subgroup.closure (Set.range a) = fA.range := by
    rw [ha_range,
      ← MonoidHom.map_closure fA (Set.range (fun j : Fin 3 => (CoxeterMatrix.A 3).simple j)),
      hgenA, Subgroup.map_top]
  have hord01 : orderOf (a 0 * a 1) = 3 := by
    have h01 : (CoxeterMatrix.A 3) (0 : Fin 3) 1 = 3 := by decide
    calc orderOf (a 0 * a 1)
        = orderOf (fA ((CoxeterMatrix.A 3).simple 0 * (CoxeterMatrix.A 3).simple 1)) := by
          simp [a]
      _ = orderOf ((CoxeterMatrix.A 3).simple 0 * (CoxeterMatrix.A 3).simple 1) :=
          orderOf_injective fA hfA_inj _
      _ = 3 := by
          simpa [h01] using
            (CoxeterMatrix.A 3).toCoxeterSystem.orderOf_simple_mul_simple (0 : Fin 3) 1
  have hord12 : orderOf (a 1 * a 2) = 3 := by
    have h12 : (CoxeterMatrix.A 3) (1 : Fin 3) 2 = 3 := by decide
    calc orderOf (a 1 * a 2)
        = orderOf (fA ((CoxeterMatrix.A 3).simple 1 * (CoxeterMatrix.A 3).simple 2)) := by
          simp [a]
      _ = orderOf ((CoxeterMatrix.A 3).simple 1 * (CoxeterMatrix.A 3).simple 2) :=
          orderOf_injective fA hfA_inj _
      _ = 3 := by
          simpa [h12] using
            (CoxeterMatrix.A 3).toCoxeterSystem.orderOf_simple_mul_simple (1 : Fin 3) 2
  have hord02 : orderOf (a 0 * a 2) = 2 := by
    have h02 : (CoxeterMatrix.A 3) (0 : Fin 3) 2 = 2 := by decide
    calc orderOf (a 0 * a 2)
        = orderOf (fA ((CoxeterMatrix.A 3).simple 0 * (CoxeterMatrix.A 3).simple 2)) := by
          simp [a]
      _ = orderOf ((CoxeterMatrix.A 3).simple 0 * (CoxeterMatrix.A 3).simple 2) :=
          orderOf_injective fA hfA_inj _
      _ = 2 := by
          simpa [h02] using
            (CoxeterMatrix.A 3).toCoxeterSystem.orderOf_simple_mul_simple (0 : Fin 3) 2
  refine ⟨a, ha_refl, hord01, hord12, hord02, ?_⟩
  intro w
  rw [hclosure]
  exact (hmem_fA w).symm

theorem ggF4H5Pos_B3_transport {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {A AK : Subgroup (MulAut ↥Bs)} (e : CoxeterMatrix.F₄.Group ≃* ↥A)
    (hAK : AK ≤ A) (hB : GGWeylOfType p (CoxeterMatrix.B 3) AK)
    (hconv : ∀ w : CoxeterMatrix.F₄.Group,
      GGIsReflection p ((e w : ↥A) : MulAut ↥Bs) →
        (CoxeterMatrix.F₄.toCoxeterSystem).IsReflection w) :
    ∃ b : Fin 3 → CoxeterMatrix.F₄.Group,
      (∀ j, (CoxeterMatrix.F₄.toCoxeterSystem).IsReflection (b j)) ∧
      (∀ j, ((e (b j) : ↥A) : MulAut ↥Bs) ∈ AK) ∧
      orderOf (b 0 * b 1) = 3 ∧ orderOf (b 1 * b 2) = 4 ∧
      orderOf (b 0 * b 2) = 2 := by
  obtain ⟨eBK, hreflBK⟩ := hB
  let fB : (CoxeterMatrix.B 3).Group →* CoxeterMatrix.F₄.Group :=
    (e.symm : ↥A →* CoxeterMatrix.F₄.Group).comp
      ((Subgroup.inclusion hAK).comp (eBK : (CoxeterMatrix.B 3).Group →* ↥AK))
  let b : Fin 3 → CoxeterMatrix.F₄.Group :=
    fun j => fB ((CoxeterMatrix.B 3).simple j)
  have hfB_inj : Function.Injective fB := by
    intro x y hxy
    have h1 : Subgroup.inclusion hAK (eBK x) = Subgroup.inclusion hAK (eBK y) := by
      have h2 := congrArg e hxy
      simpa [fB] using h2
    exact eBK.injective (Subgroup.inclusion_injective hAK h1)
  have hb_refl : ∀ j, (CoxeterMatrix.F₄.toCoxeterSystem).IsReflection (b j) := by
    intro j
    refine hconv (b j) ?_
    have hx : e (b j) =
        Subgroup.inclusion hAK (eBK ((CoxeterMatrix.B 3).simple j)) := by
      simp [b, fB]
    rw [hx]
    simpa using hreflBK j
  have hb_mem : ∀ j, ((e (b j) : ↥A) : MulAut ↥Bs) ∈ AK := by
    intro j
    have hx : e (b j) =
        Subgroup.inclusion hAK (eBK ((CoxeterMatrix.B 3).simple j)) := by
      simp [b, fB]
    rw [hx]
    exact (eBK ((CoxeterMatrix.B 3).simple j)).2
  have hord01 : orderOf (b 0 * b 1) = 3 := by
    have h01 : (CoxeterMatrix.B 3) (0 : Fin 3) 1 = 3 := by decide
    calc orderOf (b 0 * b 1)
        = orderOf (fB ((CoxeterMatrix.B 3).simple 0 * (CoxeterMatrix.B 3).simple 1)) := by
          simp [b]
      _ = orderOf ((CoxeterMatrix.B 3).simple 0 * (CoxeterMatrix.B 3).simple 1) :=
          orderOf_injective fB hfB_inj _
      _ = 3 := by
          simpa [h01] using
            (CoxeterMatrix.B 3).toCoxeterSystem.orderOf_simple_mul_simple (0 : Fin 3) 1
  have hord12 : orderOf (b 1 * b 2) = 4 := by
    have h12 : (CoxeterMatrix.B 3) (1 : Fin 3) 2 = 4 := by decide
    calc orderOf (b 1 * b 2)
        = orderOf (fB ((CoxeterMatrix.B 3).simple 1 * (CoxeterMatrix.B 3).simple 2)) := by
          simp [b]
      _ = orderOf ((CoxeterMatrix.B 3).simple 1 * (CoxeterMatrix.B 3).simple 2) :=
          orderOf_injective fB hfB_inj _
      _ = 4 := by
          simpa [h12] using
            (CoxeterMatrix.B 3).toCoxeterSystem.orderOf_simple_mul_simple (1 : Fin 3) 2
  have hord02 : orderOf (b 0 * b 2) = 2 := by
    have h02 : (CoxeterMatrix.B 3) (0 : Fin 3) 2 = 2 := by decide
    calc orderOf (b 0 * b 2)
        = orderOf (fB ((CoxeterMatrix.B 3).simple 0 * (CoxeterMatrix.B 3).simple 2)) := by
          simp [b]
      _ = orderOf ((CoxeterMatrix.B 3).simple 0 * (CoxeterMatrix.B 3).simple 2) :=
          orderOf_injective fB hfB_inj _
      _ = 2 := by
          simpa [h02] using
            (CoxeterMatrix.B 3).toCoxeterSystem.orderOf_simple_mul_simple (0 : Fin 3) 2
  exact ⟨b, hb_refl, hb_mem, hord01, hord12, hord02⟩

end CFSG.StandardType

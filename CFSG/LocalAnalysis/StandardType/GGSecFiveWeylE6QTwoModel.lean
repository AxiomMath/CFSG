module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCartan
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoModelAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoModelRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoModelSpinor
public import Mathlib.GroupTheory.GroupAction.Quotient

public section

namespace CFSG.StandardType.E6QTwo

open Module
open CFSG.Blueprint.Chevalley

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

@[expose] noncomputable def e6Weyl {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V}
    (hα : ∀ i, α i (h i) = 2) : Subgroup (V ≃ₗ[ZMod 3] V) :=
  Subgroup.closure (Set.range fun i => reflection (hα i))

variable [Finite V] {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V}
  {B : LinearMap.BilinForm (ZMod 3) V}

theorem orbit_cases (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {v : V} (hv : v ≠ 0) :
    (B v v = 2 ∧ Nat.card (MulAction.orbit (e6Weyl hα) v) = 72) ∨
      (B v v = 0 ∧ Nat.card (MulAction.orbit (e6Weyl hα) v) = 80) ∨
      (B v v = 1 ∧ Nat.card (MulAction.orbit (e6Weyl hα) v) = 90) := by
  have hsub : e6ModelWeyl hα = e6Weyl hα := rfl
  have hres := e6ModelOrbitCases hP hV hB hα (v := v) hv
  rw [hsub] at hres
  exact hres

theorem exists_mem_e6Weyl_reflection (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {v : V} (hv : B v v = 2) :
    ∃ g ∈ e6Weyl hα, ∀ u, g u = u - B v u • v := by
  have hsub : e6ModelWeyl hα = e6Weyl hα := rfl
  obtain ⟨g, hg, hgu⟩ := e6ModelExistsMemReflection hP hV hB hα (v := v) hv
  rw [hsub] at hg
  exact ⟨g, hg, hgu⟩

theorem not_mem_e6Weyl_reflection (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {v : V} (hv : B v v = 1) {g : V ≃ₗ[ZMod 3] V} (hg : g ∈ e6Weyl hα) :
    ¬ ∀ u, g u = u + B v u • v := by
  intro hformula
  have hsub : e6ModelWeyl hα = e6Weyl hα := rfl
  have hg' : g ∈ e6ModelWeyl hα := by rw [hsub]; exact hg
  exact e6ModelNotMemRefl hP hV hB hα hv hg' hformula

end CFSG.StandardType.E6QTwo

end

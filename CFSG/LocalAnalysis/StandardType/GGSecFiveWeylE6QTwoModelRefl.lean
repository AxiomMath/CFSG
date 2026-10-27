module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoModelAux

open Module
open CFSG.StandardType
open CFSG.StandardType.NoOffRest
open CFSG.StandardType.TableBExc.E6Three
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley

public section

namespace CFSG.StandardType.E6QTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin Tag.E6.rank → V} {α : Fin Tag.E6.rank → Dual (ZMod 3) V}
  {B : LinearMap.BilinForm (ZMod 3) V}

theorem e6ModelExistsMemReflection
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) (hV : Nat.card V = 3 ^ 5)
    (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2) {v : V} (hv : B v v = 2) :
    ∃ g ∈ e6ModelWeyl hα, ∀ u, g u = u - B v u • v := by
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0] at hv
    simp at hv
    exact absurd hv (by decide)
  have hxmem : (e6ModelCoord hP hV (h 0) : Fin Tag.E6.rank → ZMod 3) ∈ hypE6 :=
    mem_hypE6.mpr (e6ModelCoord hP hV (h 0)).2
  have hxne : (e6ModelCoord hP hV (h 0) : Fin Tag.E6.rank → ZMod 3) ≠ 0 := by
    intro h0
    have h1 : e6ModelCoord hP hV (h 0) = 0 := Subtype.ext h0
    have h2 : e6ModelCoord hP hV (h 0) = e6ModelCoord hP hV 0 := by simpa using h1
    have h3 : h 0 = 0 := (e6ModelCoord hP hV).injective h2
    have h4 : B (h 0) (h 0) = 2 := by
      rw [hB 0 (h 0), hα 0]
    rw [h3] at h4
    simp at h4
    exact absurd h4 (by decide)
  have hymem : (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3) ∈ hypE6 :=
    mem_hypE6.mpr (e6ModelCoord hP hV v).2
  have hyne : (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3) ≠ 0 := by
    intro h0
    apply hv0
    have h1 : e6ModelCoord hP hV v = 0 := Subtype.ext h0
    have h2 : e6ModelCoord hP hV v = e6ModelCoord hP hV 0 := by simpa using h1
    exact (e6ModelCoord hP hV).injective h2
  have hQx : e6ModelForm (e6ModelCoord hP hV (h 0) : Fin Tag.E6.rank → ZMod 3)
      (e6ModelCoord hP hV (h 0) : Fin Tag.E6.rank → ZMod 3) = 1 := by
    rw [e6ModelForm_e6Coord hP hV hB, hB 0 (h 0), hα 0]
    decide
  have hQy : e6ModelForm (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3)
      (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3) = 1 := by
    rw [e6ModelForm_e6Coord hP hV hB, hv]
    decide
  have hOrb := ggE6IsoOrbit_eq hxmem hxne
  have hyRange : (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3) ∈
      Set.range fun w : WeylGroup .E6 =>
        adAct .E6 3 w (e6ModelCoord hP hV (h 0) : Fin Tag.E6.rank → ZMod 3) := by
    rw [hOrb]
    exact ⟨hymem, hyne, hQy.trans hQx.symm⟩
  obtain ⟨w, hw⟩ := hyRange
  obtain ⟨g, hg, hgu⟩ := exists_mem_e6Weyl_of_adAct hP hV hα w
  have hg0 : g (h 0) = v := by
    apply (e6ModelCoord hP hV).injective
    apply Subtype.ext
    rw [hgu (h 0)]
    exact hw
  have hiso : ∀ u v : V, B (g u) (g v) = B u v :=
    e6ModelWeyl_isometry hP hV hB hα hg
  refine Exists.intro (g * reflection (hα 0) * g⁻¹) ?_
  constructor
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg
      (Subgroup.subset_closure ⟨0, rfl⟩)) (Subgroup.inv_mem _ hg)
  · intro u
    have hcoe : α 0 (g⁻¹ u) = B v u := by
      rw [← hB 0 (g⁻¹ u)]
      have h' := hiso (h 0) (g⁻¹ u)
      simpa [hg0] using h'.symm
    rw [show (g * reflection (hα 0) * g⁻¹) u = g (reflection (hα 0) (g⁻¹ u)) from rfl,
      Module.reflection_apply, map_sub, map_smul, hg0, hcoe]
    simp

end CFSG.StandardType.E6QTwo

end

module

public import CFSG.LocalAnalysis.StandardType.GGKOnlyE6Normalization

public section

namespace CFSG.StandardType

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem e6_dependent_d5_span_general
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hdep : ¬ LinearIndependent (ZMod 3) h) :
    ∃ c : Fin 5 → ZMod 3, h 0 = ∑ i : Fin 5, c i • h (d5Index i) := by
  classical
  let W : Submodule (ZMod 3) V :=
    Submodule.span (ZMod 3) (Set.range (fun i : Fin 5 => h (d5Index i)))
  have hW : LinearIndependent (ZMod 3) (fun i : Fin 5 => h (d5Index i)) :=
    d5_roots_linearIndependent hpair
  have h0W : h 0 ∈ W := by
    by_contra hnot
    have hcons : LinearIndependent (ZMod 3)
        (Fin.cons (h 0) (fun i : Fin 5 => h (d5Index i))) :=
      hW.finCons (x := h 0) hnot
    have hEq : Fin.cons (h 0) (fun i : Fin 5 => h (d5Index i)) = h := by
      funext i
      fin_cases i <;> rfl
    exact hdep (by simpa only [hEq] using hcons)
  rw [Submodule.mem_span_range_iff_exists_fun] at h0W
  obtain ⟨c, hc⟩ := h0W
  exact ⟨c, hc.symm⟩


theorem e6_dependent_d5_span
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V} {y : V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hy : y ≠ 0) (hker : ∀ i, α i y = 0)
    (hdim : Module.finrank (ZMod 3) V = 6)
    (hdep : ¬ LinearIndependent (ZMod 3) h) :
    ∃ c : Fin 5 → ZMod 3, h 0 = ∑ i : Fin 5, c i • h (d5Index i) :=
  e6_dependent_d5_span_general hpair hdep

theorem e6_dependent_d5_span_reindex_general
    {Λ : Type} (e : Fin 6 ≃ Λ)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Λ → V} {α : Λ → Module.Dual (ZMod 3) V}
    (hpair : ∀ i j, α (e i) (h (e j)) = (CartanMatrix.E 6 i j : ZMod 3))
    (hdep : ¬ LinearIndependent (ZMod 3) (fun i : Fin 6 => h (e i))) :
    ∃ c : Fin 5 → ZMod 3, h (e 0) = ∑ i : Fin 5, c i • h (e (d5Index i)) := by
  let h' : Fin 6 → V := fun i => h (e i)
  let α' : Fin 6 → Module.Dual (ZMod 3) V := fun i => α (e i)
  have hpair' : ∀ i j, α' i (h' j) = (CartanMatrix.E 6 i j : ZMod 3) := hpair
  obtain ⟨c, hc⟩ := e6_dependent_d5_span_general (h := h') (α := α') hpair' hdep
  exact ⟨c, hc⟩


theorem e6_dependent_d5_span_reindex
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin 6 ≃ Λ)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    {h : Λ → V} {α : Λ → Module.Dual (ZMod 3) V} {y : V}
    (hpair : ∀ i j, α (e i) (h (e j)) = (CartanMatrix.E 6 i j : ZMod 3))
    (hy : y ≠ 0) (hker : ∀ i : Fin 6, α (e i) y = 0)
    (hdim : Module.finrank (ZMod 3) V = 6)
    (hdep : ¬ LinearIndependent (ZMod 3) (fun i : Fin 6 => h (e i))) :
    ∃ c : Fin 5 → ZMod 3, h (e 0) = ∑ i : Fin 5, c i • h (e (d5Index i)) :=
  e6_dependent_d5_span_reindex_general e hpair hdep

end CFSG.StandardType

end

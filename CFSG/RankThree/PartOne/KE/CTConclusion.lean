module

public import CFSG.RankThree.PartOne.KE.CTStatement

public section

namespace CFSG.RankThree.PartOne.KE

variable {C : Type} [Group C] {p n₀ d : ℕ}

theorem CyclicSylowConclusion'.pgroups_cyclic (h : CyclicSylowConclusion' C p n₀ d) :
    ∀ Q : Subgroup C, IsPGroup p Q → IsCyclic Q := by
  obtain ⟨-, -, -, -, -, h5, -, -⟩ := h
  exact h5

theorem CyclicSylowConclusion'.centralizer_cyclic (h : CyclicSylowConclusion' C p n₀ d) :
    ∀ x : C, orderOf x = p → IsCyclic (Subgroup.centralizer {x}) := by
  obtain ⟨T, hT, -, -, -, -, -, h7⟩ := h
  intro x hx
  obtain ⟨g, -, hg⟩ := h7 x hx
  let φ : Subgroup.centralizer {x} →* T :=
    ((MulAut.conj g).toMonoidHom.comp (Subgroup.centralizer {x}).subtype).codRestrict T
      fun y => by
        rw [← hg]
        have hy := Subgroup.mem_centralizer_singleton_iff.1 y.2
        rw [Subgroup.mem_centralizer_singleton_iff]
        change g * y * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * y * g⁻¹)
        calc g * y * g⁻¹ * (g * x * g⁻¹) = g * ((y : C) * x) * g⁻¹ := by group
          _ = g * (x * (y : C)) * g⁻¹ := by rw [hy]
          _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  refine isCyclic_of_injective φ fun a b hab => ?_
  have h1 : g * (a : C) * g⁻¹ = g * (b : C) * g⁻¹ :=
    congrArg Subtype.val hab
  exact Subtype.ext ((MulAut.conj g).injective h1)

end CFSG.RankThree.PartOne.KE

module

public import CFSG.OddTranspositions.Width

public section

namespace CFSG.OddTranspositions

variable {G : Type*} [Group G] {D : Set G}

theorem not_exists_mul_mem_of_widthLe_two (hW : WidthLe D 2)
    (hne : ∀ d ∈ D, d ≠ 1) :
    ¬ ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D := by
  classical
  rintro ⟨u, huD, v, hvD, huv, hcomm, huvD⟩
  have h1 : u ∉ ({v, u * v} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact huv h
    · have hv1 : v = 1 := by
        have := congrArg (fun x => u⁻¹ * x) h.symm
        simpa using this
      exact hne v hvD hv1
  have h2 : v ∉ ({u * v} : Finset G) := by
    simp only [Finset.mem_singleton]
    intro h
    have hu1 : u = 1 := by
      have := congrArg (fun x => x * v⁻¹) h.symm
      simpa using this
    exact hne u huD hu1
  have hcard : ({u, v, u * v} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_singleton]
  have hsub : (({u, v, u * v} : Finset G) : Set G) ⊆ D := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact huD
    · exact hvD
    · exact huvD
  have hpair : ∀ x ∈ ({u, v, u * v} : Finset G), ∀ y ∈ ({u, v, u * v} : Finset G),
      x ≠ y → Commute x y := by
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
    · exact absurd (hx.trans hy.symm) hxy
    · rw [hx, hy]; exact hcomm
    · rw [hx, hy]; exact (Commute.refl u).mul_right hcomm
    · rw [hx, hy]; exact hcomm.symm
    · exact absurd (hx.trans hy.symm) hxy
    · rw [hx, hy]; exact (hcomm.symm).mul_right (Commute.refl v)
    · rw [hx, hy]; exact ((Commute.refl u).mul_right hcomm).symm
    · rw [hx, hy]; exact ((hcomm.symm).mul_right (Commute.refl v)).symm
    · exact absurd (hx.trans hy.symm) hxy
  have := hW _ hsub hpair
  omega

end CFSG.OddTranspositions

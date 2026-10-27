module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphD5Fin

public section

namespace CFSG.StandardType

@[expose] def ggg5x_x : Fin 5 → ZMod 3 := ![1, 2, 2, 1, 1]

theorem ggg5x_x_ne : ggg5x_x ≠ 0 := by decide +kernel

theorem ggg5x_x_fixed : ∀ j : Fin 5, j ≠ 1 → ggg5_S j ggg5x_x = ggg5x_x := by decide +kernel

theorem ggg5x_S_factorA1 (v : Fin 5 → ZMod 3) (hv : v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0)
    (j : Fin 5) (hj : j ≠ 1) :
    ggg5_S j v 1 = 0 ∧ ggg5_S j v 2 = 0 ∧ ggg5_S j v 3 = 0 ∧ ggg5_S j v 4 = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  fin_cases j <;> simp_all [ggg5_S, ggg5_C, Fin.sum_univ_five]

theorem ggg5x_S_factorA3 (v : Fin 5 → ZMod 3) (hv : v 0 = 0 ∧ v 1 = 0) (j : Fin 5)
    (hj : j ≠ 1) : ggg5_S j v 0 = 0 ∧ ggg5_S j v 1 = 0 := by
  obtain ⟨h0, h1⟩ := hv
  fin_cases j <;> simp_all [ggg5_S, ggg5_C, Fin.sum_univ_five]

theorem ggg5x_cert (g gi : Fin 5 → Fin 5) (hg : ggg5_pair g gi) (s t : ZMod 3)
    (hs : s = 1 ∨ s = 2) (ht : t = 1 ∨ t = 2) :
    ∃ l : List (Fin 5), (l = [] ∨ l = [3, 2, 1] ∨ l = [4, 2, 1]) ∧
      (ggg5_N g gi l s t ggg5x_x = ggg5x_x ∨ ggg5_N g gi l s t ggg5x_x = -ggg5x_x) ∧
      ggg5_N g gi l s t (Pi.single 0 1) 0 ≠ 0 ∧ ggg5_N g gi l s t (Pi.single 0 1) 1 = 0 ∧
      (ggg5_N g gi l s t (Pi.single 0 1) 2 ≠ 0 ∨ ggg5_N g gi l s t (Pi.single 0 1) 3 ≠ 0 ∨
        ggg5_N g gi l s t (Pi.single 0 1) 4 ≠ 0) := by
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hs with rfl | rfl <;>
    rcases ht with rfl | rfl
  · exact ⟨[3, 2, 1], .inr (.inl rfl), by decide +kernel⟩
  · exact ⟨[], .inl rfl, by decide +kernel⟩
  · exact ⟨[], .inl rfl, by decide +kernel⟩
  · exact ⟨[3, 2, 1], .inr (.inl rfl), by decide +kernel⟩
  · exact ⟨[3, 2, 1], .inr (.inl rfl), by decide +kernel⟩
  · exact ⟨[], .inl rfl, by decide +kernel⟩
  · exact ⟨[], .inl rfl, by decide +kernel⟩
  · exact ⟨[3, 2, 1], .inr (.inl rfl), by decide +kernel⟩
  · exact ⟨[4, 2, 1], .inr (.inr rfl), by decide +kernel⟩
  · exact ⟨[], .inl rfl, by decide +kernel⟩
  · exact ⟨[], .inl rfl, by decide +kernel⟩
  · exact ⟨[4, 2, 1], .inr (.inr rfl), by decide +kernel⟩

end CFSG.StandardType

end

module

public import CFSG.Quasithin.Background.FLcModel

public section

namespace CFSG.Quasithin.FLc

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem isPGroup_Ut {n : ℕ} (hn : 1 ≤ n) : IsPGroup 2 ↥(Ut n) := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 hn
  have h := P.isPGroup'
  rw [hP] at h
  exact h

theorem mem_Ut_of_fixes {n : ℕ} {g : SLt n}
    (hst : ∀ j, 2 ≤ j → j < n → g ∈ stabilizer (flagSpace n (ZMod 2) j))
    (hfix : ∀ v ∈ flagSpace n (ZMod 2) 2, mat g *ᵥ v = v) : g ∈ Ut n := by
  have h1 : g ∈ stabilizer (flagSpace n (ZMod 2) 1) := by
    rw [mem_stabilizer]
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h := hfix w (flagSpace_mono (by norm_num) hw)
      have h' : (mulVecLin (mat g)) w = w := h
      rw [h']
      exact hw
    · intro hv
      refine ⟨v, hv, ?_⟩
      exact hfix v (flagSpace_mono (by norm_num) hv)
  rw [Ut_eq_QI, mem_flagStabilizer]
  intro i hi
  rcases Nat.lt_or_ge i 2 with h | h
  · have hi1 : i = 1 := by
      have := hi.1
      omega
    subst hi1
    exact h1
  · exact hst i h hi.2

theorem reflection_mem_stab {n j : ℕ} (hn : 2 ≤ n) (hne : j ≠ 1) :
    reflection n (ZMod 2) 1 le_rfl (by omega) ∈ stabilizer (flagSpace n (ZMod 2) j) := by
  have h := (reflection_mem_QI (n := n) (I := {j}) (i := 1) ⟨le_rfl, by omega⟩).2
    (by simpa [eq_comm] using hne)
  rw [QI, mem_flagStabilizer] at h
  exact h j rfl

theorem reflection_notMem_stab {n : ℕ} (hn : 2 ≤ n) :
    reflection n (ZMod 2) 1 le_rfl (by omega) ∉ stabilizer (flagSpace n (ZMod 2) 1) :=
  reflection_notMem_stabilizer le_rfl (by omega)

end CFSG.Quasithin.FLc

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S143Aux

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q3B

theorem vec3_injective (a b c : Fin 6) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]

theorem alt_three_trans (a b c a' b' c' : Fin 6) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hab' : a' ≠ b') (hac' : a' ≠ c') (hbc' : b' ≠ c') :
    ∃ σ ∈ alternatingGroup (Fin 6), σ a = a' ∧ σ b = b' ∧ σ c = c' := by
  have h4 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 6)) (Fin 6) 4 := by
    simpa using alternatingGroup.isMultiplyPretransitive (Fin 6)
  have h3 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 6)) (Fin 6) 3 :=
    MulAction.isMultiplyPretransitive_of_le (n := 4) (by norm_num) (by simp)
  rw [MulAction.isMultiplyPretransitive_iff] at h3
  obtain ⟨g, hg⟩ := h3 ⟨![a, b, c], vec3_injective a b c hab hac hbc⟩
    ⟨![a', b', c'], vec3_injective a' b' c' hab' hac' hbc'⟩
  have h0 := congrArg (fun e : Fin 3 ↪ Fin 6 => e 0) hg
  have h1 := congrArg (fun e : Fin 3 ↪ Fin 6 => e 1) hg
  have h2 := congrArg (fun e : Fin 3 ↪ Fin 6 => e 2) hg
  refine ⟨g, g.2, ?_, ?_, ?_⟩
  · simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h0
  · simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h1
  · simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h2

end Q3B

theorem exists_alt_mapsto (i j : Fin 6) (hij : i ≠ j) :
    ∃ ρ ∈ alternatingGroup (Fin 6), ρ i = 4 ∧ ρ j = 5 := by
  have hk : ∀ i j : Fin 6, ∃ k : Fin 6, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k, hki, hkj⟩ := hk i j
  obtain ⟨σ, hσ, h1, h2, -⟩ := Q3B.alt_three_trans i j k 4 5 0 hij hki.symm hkj.symm
    (by decide) (by decide) (by decide)
  exact ⟨σ, hσ, h1, h2⟩

end S153Q

end CFSG.Quasithin

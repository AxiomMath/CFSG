module

public import CFSG.LocalAnalysis.StandardType.GGWAutSym
public import CFSG.LocalAnalysis.StandardType.GGWAutMonoNorm
public import CFSG.LocalAnalysis.StandardType.GGWAutOrthOdd
public import CFSG.LocalAnalysis.StandardType.GGWAutE

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggWAut_engine (hK : GGReflClassOmegaInput) : GGWAutEngine := by
  intro V _ _ _ n hdim hn A hTF habs
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRA : reflGp A ≤ A := ggWAut_reflGp_le A
  have hgen : reflGp A = Subgroup.closure {r | r ∈ reflGp A ∧ GGLinRefl r} :=
    ggWAut_reflGp_closure A
  by_cases h9 : 9 ≤ n
  · rcases hK.1 3 (by norm_num) V n hdim h9 (reflGp A) habs hgen with
      h1 | h2 | h3 | h4 | h5
    · exact Or.inr (ggWAut_imprim (by omega) A (reflGp A) hRA rfl habs h1)
    · exfalso
      exact ggWAut_SL_has_transvection (by omega) A (fun g hg => hRA (h2.1 g hg)) hTF
    · by_cases hEven : Even n
      · exact Or.inl ⟨hEven, h3.1⟩
      · have hodd : Odd (Module.finrank (ZMod 3) V) := by
          rw [hdim]
          exact Nat.not_even_iff_odd.mp hEven
        exact Or.inr (ggWAut_orthOdd hodd A (reflGp A) hRA rfl habs h3.1)
    · rcases h4 with ⟨_, e, he⟩
      exact Or.inr (ggWAut_sym (N := n + 1) (by omega) A (reflGp A) hRA rfl habs e he)
    · rcases h5 with ⟨_, e, he⟩
      exact Or.inr (ggWAut_sym (N := n + 2) (by omega) A (reflGp A) hRA rfl habs e he)
  · have hn8 : n ≤ 8 := by omega
    rcases hK.2 V n hdim hn hn8 (reflGp A) habs hgen with
      h1 | h2 | h3 | h4 | h5 | h6 | h7
    · exact Or.inr (ggWAut_imprim (by omega) A (reflGp A) hRA rfl habs h1)
    · exfalso
      exact ggWAut_SL_has_transvection (by omega) A (fun g hg => hRA (h2.1 g hg)) hTF
    · by_cases hEven : Even n
      · exact Or.inl ⟨hEven, h3.1⟩
      · have hodd : Odd (Module.finrank (ZMod 3) V) := by
          rw [hdim]
          exact Nat.not_even_iff_odd.mp hEven
        exact Or.inr (ggWAut_orthOdd hodd A (reflGp A) hRA rfl habs h3.1)
    · rcases h4 with ⟨_, e, he⟩
      exact Or.inr (ggWAut_sym (N := n + 1) (by omega) A (reflGp A) hRA rfl habs e he)
    · rcases h5 with ⟨_, e, he⟩
      exact Or.inr (ggWAut_sym (N := n + 2) (by omega) A (reflGp A) hRA rfl habs e he)
    · rcases h6 with ⟨_, hW⟩
      exact Or.inr (ggWAut_E7 A (reflGp A) hRA rfl habs hW)
    · rcases h7 with ⟨_, hW⟩
      exact Or.inr (ggWAut_E8 A (reflGp A) hRA rfl habs hW)

end CFSG.StandardType

end

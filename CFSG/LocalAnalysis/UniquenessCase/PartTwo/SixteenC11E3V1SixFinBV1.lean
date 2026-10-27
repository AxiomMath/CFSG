module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6 Equiv

private theorem s1611e3_sixZ_ne_one : sixZ ≠ (1 : SixE6) := by
  decide +kernel

private theorem s1611e3_sixRho_ne_swap_mul (σ σ' : Perm (Fin 6)) :
    sixRho σ ≠ sixSwap * sixRho σ' := by
  intro h
  have h1 := congrArg (fun f : MulAut (SixE6 × SixE6) => f (sixZ, 1)) h
  have h2 : ((coreAct 6 σ) sixZ, (coreAct 6 (sixAlpha σ)) 1) =
      ((coreAct 6 (sixAlpha σ')) 1, (coreAct 6 σ') sixZ) := by
    rw [show (sixRho σ) (sixZ, 1) =
          ((coreAct 6 σ) sixZ, (coreAct 6 (sixAlpha σ)) 1) from rfl,
      show (sixSwap * sixRho σ') (sixZ, 1) =
          ((coreAct 6 (sixAlpha σ')) 1, (coreAct 6 σ') sixZ) from rfl] at h1
    exact h1
  have h3 : (coreAct 6 σ) sixZ = (1 : SixE6) := by
    simpa using congrArg Prod.fst h2
  have h4 : sixZ = (1 : SixE6) := by
    apply (coreAct 6 σ).injective
    rw [h3, map_one]
  exact s1611e3_sixZ_ne_one h4

theorem s1611e3_sixGhatOf_injective {c d : s1611e3_SixCode} (hc : s1611e3_sixCodeValid c)
    (hd : s1611e3_sixCodeValid d) (h : s1611e3_sixGhatOf c = s1611e3_sixGhatOf d) : c = d := by
  obtain ⟨σ, τ, ε⟩ := c
  obtain ⟨σ', τ', ε'⟩ := d
  simp only [s1611e3_sixCodeValid] at hc hd
  rw [show τ = sixAlpha σ from hc, show τ' = sixAlpha σ' from hd]
  cases ε <;> cases ε' <;>
    simp only [s1611e3_sixGhatOf, Bool.false_eq_true, if_true, if_false, reduceIte] at h
  · rw [sixRho_injective h]
  · exact absurd h (s1611e3_sixRho_ne_swap_mul σ σ')
  · refine absurd ?_ (s1611e3_sixRho_ne_swap_mul σ σ')
    rw [← h, ← mul_assoc, sixSwap_mul_self, one_mul]
  · rw [sixRho_injective (mul_left_cancel h)]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

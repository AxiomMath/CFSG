module

public import CFSG.RankThree.PartTwo.Sec21.FF81P51Core
public import CFSG.LocalAnalysis.StandardType.FS81.SpMatAlg

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.P51

open Matrix
open CFSG.StandardType.FrameRoute.FS81 (spMat)

private theorem spMat_mem_H0L : ∀ σ : Equiv.Perm (Fin 4), ∀ ε : Fin 4 → ZMod 3,
    (∀ i, ε i ≠ 0) → σ 0 = 0 → spMat σ ε ∈ H0L := by
  decide +kernel

private theorem swap_mem_H0L : ∀ m : Fin 4, m ≠ 0 →
    spMat (Equiv.swap 1 m) 1 ∈ H0L ∧ spMat (Equiv.swap 1 m) 1 * spMat (Equiv.swap 1 m) 1 = 1 := by
  decide +kernel

private theorem swap_mul_sig01_mem_H0L : ∀ σ : Equiv.Perm (Fin 4), ∀ ε : Fin 4 → ZMod 3,
    (∀ i, ε i ≠ 0) → σ 0 ≠ 0 →
    spMat σ ε * spMat (Equiv.swap 1 (σ⁻¹ 0)) 1 * Sig01 ∈ H0L := by
  decide +kernel

private theorem sig01_mul_self : Sig01 * Sig01 = 1 := by decide +kernel

theorem mon_mem_GM {Γ : Subgroup GL4} (h : Hyp Γ)
    (hs : Sig01 ∈ GM Γ) (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ZMod 3) (hε : ∀ i, ε i ≠ 0) :
    spMat σ ε ∈ GM Γ := by
  by_cases h0 : σ 0 = 0
  · exact H0L_sub h _ (spMat_mem_H0L σ ε hε h0)
  · have hm : σ⁻¹ 0 ≠ 0 := fun hm => h0 (by simpa using (congrArg σ hm).symm)
    obtain ⟨hP, hPP⟩ := swap_mem_H0L (σ⁻¹ 0) hm
    have hQ := swap_mul_sig01_mem_H0L σ ε hε h0
    have hA : spMat σ ε = (spMat σ ε * spMat (Equiv.swap 1 (σ⁻¹ 0)) 1 * Sig01) * Sig01 *
        spMat (Equiv.swap 1 (σ⁻¹ 0)) 1 := by
      simp only [mul_assoc]
      rw [← mul_assoc Sig01 Sig01, sig01_mul_self, one_mul, hPP, mul_one]
    rw [hA]
    exact (GM Γ).mul_mem ((GM Γ).mul_mem (H0L_sub h _ hQ) hs) (H0L_sub h _ hP)

end CFSG.RankThree.PartTwo.Sec21.FF81.P51

end

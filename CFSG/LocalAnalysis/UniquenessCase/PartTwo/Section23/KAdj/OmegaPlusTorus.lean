module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Concl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaPlusClosure
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLTwoConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open scoped MatrixGroups

theorem kAdjConcl_plusTorus {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {r : ℕ} (hr : Odd r) {c : Kˣ} (hord : orderOf c = r) :
    KAdjConcl (Hinf (plusFlagStab K 3 ({1} : Finset ℕ))) (torusElt 3 K ![c, c⁻¹, 1]) r n := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨b, hb, hbo⟩ := exists_sq_eq_inv_of_odd_orderOf (c := c) (by rwa [hord])
  refine ⟨(plusRootEmbTwo K).range, (plusRootEmbOne K).range,
    plusRootEmbTwo_range_le_hinf hK4, plusRootEmbOne_range_le_hinf hK4, ?_, ?_⟩
  · intro N hNK hnorm h₁ h₂
    exact normal_closure_plusRoots hK4 N hNK hnorm h₁ h₂
  · rintro X (rfl | rfl)
    · exact kAdjData_of_conj (plusRootEmbTwo K) (plusRootEmbTwo_injective K)
        (isSLn_plusRootEmbTwo_range hK) (torusElt 3 K ![c, c⁻¹, 1]) (plusDiagSL2 b)
        (by rw [orderOf_plusDiagSL2, hbo, hord])
        (fun A => torusElt_mul_plusRootEmbTwo_mul_inv hb A)
    · exact kAdjData_of_conj (plusRootEmbOne K) (plusRootEmbOne_injective K)
        (isSLn_plusRootEmbOne_range hK) (torusElt 3 K ![c, c⁻¹, 1]) (plusDiagSL2 b)
        (by rw [orderOf_plusDiagSL2, hbo, hord])
        (fun A => torusElt_mul_plusRootEmbOne_mul_inv hb A)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Concl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaMinusClosure
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLTwoConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open scoped MatrixGroups

theorem kAdjConcl_omegaMinusTorus {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {r : ℕ} (hr : Odd r) {u : Kˣ} (hord : orderOf u = r) {τ : OmegaMinusE K b c}
    (hτ : ((τ : OmegaMinusE K b c) :
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) =
        prodHom (Fin 2 → K) (torusElt 3 K ![u, u⁻¹, 1])) :
    KAdjConcl (Hinf (omegaMinusTailQZero K b c)) τ r n := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨b', hb', hbo⟩ := exists_sq_eq_inv_of_odd_orderOf (c := u) (by rwa [hord])
  refine ⟨omegaMinusRoot K b c, omegaMinusRoot K b c,
    omegaMinusRoot_le_hinf hK4 b c, omegaMinusRoot_le_hinf hK4 b c, ?_, ?_⟩
  · intro N hNK hnorm h₁ _
    exact normal_closure_omegaMinusRoot hirr hK4 N hNK hnorm h₁
  · rintro X (rfl | rfl)
    · exact kAdjData_of_conj (omegaMinusRootHom K b c) (omegaMinusRootHom_injective K b c)
        (isSLn_omegaMinusRoot hK b c) τ (plusDiagSL2 b')
        (by rw [orderOf_plusDiagSL2, hbo, hord])
        (fun A => omegaMinusRootHom_conj hb' b c hτ A)
    · exact kAdjData_of_conj (omegaMinusRootHom K b c) (omegaMinusRootHom_injective K b c)
        (isSLn_omegaMinusRoot hK b c) τ (plusDiagSL2 b')
        (by rw [orderOf_plusDiagSL2, hbo, hord])
        (fun A => omegaMinusRootHom_conj hb' b c hτ A)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110h
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearFieldExport

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110h (sl_a5 a5Center_map)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  (linearFieldAut_components linear_inner_components nonempty_mulEquiv_specialFactor)

namespace LemmaOLin

open Polynomial CFSG.RankThree.PartOne.KCPrimary
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem field_case {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k] [Finite k] (σ : k ≃+* k)
    (hσ : orderOf σ = 3) (K : Subgroup (LinearFlag.projectiveSL n k))
    (hK : IsComponentOf K (fixSubgroup (LinearFlag.fieldAut n k σ)))
    (hL : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 5))) :
    n = 2 ∧ (Nat.card k = 64 ∨ Nat.card k = 125) := by
  obtain ⟨-, f, hf, hker⟩ := linearFieldAut_components hn σ K hK
  obtain ⟨hn2, hE⟩ := sl_a5 hn f hf hker hL
  have hpow := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
  rw [hσ] at hpow
  refine ⟨hn2, ?_⟩
  rcases hE with h | h <;> rw [h] at hpow
  · left; omega
  · right; omega

theorem inner_case_card_le {n : ℕ} {k : Type} [Field k] [Finite k] (hpk : ((3 : ℕ) : k) ≠ 0)
    {A : GL (Fin n) k} {c : kˣ} (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (K : Subgroup (LinearFlag.projectiveSL n k))
    (hK : IsComponentOf K (fixSubgroup (LinearFlag.conjAut n k A)))
    (hL : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 5))) :
    Nat.card k ≤ 5 := by
  obtain ⟨h, rfl⟩ := linear_inner_components hpk hA K hK
  have hsq := squarefree_minpoly_glA hpk hA
  haveI : Fact (Irreducible h.1.1) := ⟨irreducible_of_mem_primaryFactors h.1.2⟩
  haveI : Finite (AdjoinRoot h.1.1) := Module.finite_of_finite k
  obtain ⟨e⟩ := nonempty_mulEquiv_specialFactor hsq h.1.2
  obtain ⟨f, hf, hker⟩ := InputsL33.exists_surjective_ker_le_center_map_proj e
  have hm : 2 ≤ primaryMultiplicity (glA A : Module.End k (Fin n → k)) h.1.1 := by
    rcases h.2 with h3 | ⟨h2, -⟩
    · omega
    · exact h2
  obtain ⟨-, hE⟩ := sl_a5 hm f hf hker hL
  have hle : Nat.card k ≤ Nat.card (AdjoinRoot h.1.1) :=
    Nat.card_le_card_of_injective (algebraMap k (AdjoinRoot h.1.1))
      (algebraMap k (AdjoinRoot h.1.1)).injective
  omega

end LemmaOLin

end CFSG.RankThree.PartTwo.Sec21.FF79

module

public import CFSG.LocalAnalysis.StandardType.GGKGTwMult
public import CFSG.Blueprint.Catalog
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeLift
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LocalAnalysis.SectionRank.EvenCover.Unitary

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix

theorem exists_mulEquiv_statedSU_of_lieModel_PSU_four {E : Type} [Group E] {f : ℕ}
    (hE : CFSG.Blueprint.LieModel E .PSU 4 2 f) :
    1 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = (2 ^ f) ^ 2 ∧ Nonempty (E ≃* StatedSU 4 (2 ^ f) K) := by
  rcases hE with ⟨-, hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩
  · have hf : 1 ≤ f := hadm.2.1
    haveI hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
    haveI : CharP K 2 := hU.charP
    have hscal := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSU_four_eq_bot
      (K := K) (2 ^ f)
    let ε : StatedProj (StatedSU 4 (2 ^ f) K) ≃* StatedSU 4 (2 ^ f) K :=
      (QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot
    exact ⟨hf, K, hKf, hKfin, inferInstance, hcard, ⟨e.trans ε⟩⟩
  all_goals exact absurd h4 (by norm_num)

theorem kgMult_of_mulEquiv_statedSU_four
    {E F : Type} [Group E] [Field F] {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = (2 ^ f) ^ 2)
    (he : Nonempty (E ≃* StatedSU 4 (2 ^ f) F))
    (N : Type) [Group N] [Finite N] (π : N →* E) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center N) (hperf : commutator N = ⊤) :
    IsCyclic (Subgroup.center N) := by
  haveI hU : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  haveI : Finite F := hU.finite
  haveI : CharP F 2 := hU.charP
  obtain ⟨e⟩ := he
  have hπ' : Function.Surjective (e.toMonoidHom.comp π) := e.surjective.comp hπ
  have hker' : (e.toMonoidHom.comp π).ker = π.ker :=
    MonoidHom.ker_comp_of_injective π e.toMonoidHom e.injective
  exact kgMult_statedSU_four hf hF N (e.toMonoidHom.comp π) hπ' (by rw [hker']; exact hker) hperf

end CFSG.StandardType.KGL

end

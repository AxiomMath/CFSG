module

public import CFSG.LocalAnalysis.WeakClosure81.TwoConjugateSz
public import CFSG.LocalAnalysis.WeakClosure81.TwelveSubgroup
public import CFSG.LocalAnalysis.WeakClosure81.SzStructureFacts
public import CFSG.LocalAnalysis.WeakClosure81.SzStructurePair
public import CFSG.LocalAnalysis.WeakClosure81.TwelveInputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenK

open Subgroup

theorem twoConjugateGenerationSz_of_suzukiSubgroupInput
    (h : CFSG.LocalAnalysis.WeakClosure81.SuzukiSubgroupInput) : TwoConjugateGenerationSz := by
  intro S _ _ n hn hS A hA hcard
  obtain ⟨hnodd, -⟩ := odd_and_three_le_of_isSz hS
  obtain ⟨E, hEA, hE, hE4⟩ := CFSG.LocalAnalysis.WeakClosure81.exists_four_subgroup hA
    (four_le_card_of_isElemAbelian hA hcard)
  have hA1 : A ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot A).mp (by omega)
  obtain ⟨⟨a, haA⟩, ha1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have ha1 : a ≠ 1 := fun h1 => ha1' (Subtype.ext h1)
  have ha : a * a = 1 := by rw [← sq]; exact hA.2 a haA
  obtain ⟨g, hg⟩ := exists_orderOf_mul_conj_of_isSz hS ha ha1
  refine ⟨g, ?_⟩
  by_contra hU
  have haU : a ∈ A ⊔ CFSG.Quasithin.conjSubgroup A g := mem_sup_left haA
  have hbU : g⁻¹ * a * g ∈ A ⊔ CFSG.Quasithin.conjSubgroup A g := by
    refine mem_sup_right (CFSG.Quasithin.mem_conjSubgroup_iff.mpr ?_)
    simpa [mul_assoc] using haA
  have hbb : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
    calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [ha]; group
  rcases h n S hS _ hU ⟨E, hEA.trans le_sup_left, hE, hE4⟩ with ⟨Q, hQ⟩ | ⟨k, hk, hkn, hkU⟩
  · exact orderOf_mul_ne_two_pow_sub_one_of_mem_normalizer Q (hQ haU) (hQ hbU) ha hbb hn hg
  · exact orderOf_ne_two_pow_sub_one_of_isSz hkU hnodd hk hkn ⟨_, mul_mem haU hbU⟩
      ((Subgroup.orderOf_mk _ _).trans hg)

theorem twoConjugateGeneration_of_suzukiSubgroupInput
    (h : CFSG.LocalAnalysis.WeakClosure81.SuzukiSubgroupInput) : TwoConjugateGeneration :=
  twoConjugateGeneration_of_sz (twoConjugateGenerationSz_of_suzukiSubgroupInput h)

end CFSG.LocalAnalysis.WeakClosure81.SevenK

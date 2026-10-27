module

public import CFSG.Quasithin.EmptyFaithful.S151S4B
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega4
public import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open CFSG.Quasithin.S151S4 (SL2 Bsub Usub uU_sq uU_mem_Bsub mem_Usub borel_or_top)

variable {K : Type} [Field K]

private theorem isPGroup_prod_Usub_L26 [CharP K 2] :
    IsPGroup 2 ↥((Usub K).prod (Usub K)) := by
  intro x
  refine ⟨1, ?_⟩
  obtain ⟨hu, hv⟩ := Subgroup.mem_prod.mp x.2
  obtain ⟨t, ht⟩ := mem_Usub.mp hu
  obtain ⟨s, hs⟩ := mem_Usub.mp hv
  apply Subtype.ext
  show (x : SL2 K × SL2 K) ^ 2 ^ 1 = 1
  rw [pow_one, pow_two]
  apply Prod.ext
  · show (x : SL2 K × SL2 K).1 * (x : SL2 K × SL2 K).1 = 1
    rw [← ht, uU_sq]
  · show (x : SL2 K × SL2 K).2 * (x : SL2 K × SL2 K).2 = 1
    rw [← hs, uU_sq]

theorem prod_Usub_le_prod_Bsub :
    (Usub K).prod (Usub K) ≤ (Bsub K).prod (Bsub K) := by
  rintro ⟨u, v⟩ h
  obtain ⟨hu, hv⟩ := Subgroup.mem_prod.mp h
  obtain ⟨t, ht⟩ := mem_Usub.mp hu
  obtain ⟨s, hs⟩ := mem_Usub.mp hv
  refine Subgroup.mem_prod.mpr ⟨?_, ?_⟩
  · rw [← ht]; exact uU_mem_Bsub t
  · rw [← hs]; exact uU_mem_Bsub s

theorem exists_sylow_eq_prod_Usub [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    ∃ T : Sylow 2 (SL2 K × SL2 K),
      (T : Subgroup (SL2 K × SL2 K)) = (Usub K).prod (Usub K) := by
  obtain ⟨T, hT⟩ := IsPGroup.exists_le_sylow (p := 2)
    (P := (Usub K).prod (Usub K)) (isPGroup_prod_Usub_L26 (K := K))
  refine ⟨T, ?_⟩
  obtain ⟨SA, SB, hT_eq⟩ := sylow_prod_eq T
  have hcardT : Nat.card (T : Subgroup (SL2 K × SL2 K)) = Nat.card K * Nat.card K := by
    rw [hT_eq, Nat.card_congr
      (Subgroup.prodEquiv (SA : Subgroup (SL2 K)) (SB : Subgroup (SL2 K))).toEquiv,
      Nat.card_prod, card_sylow_eq_card_field K hK SA, card_sylow_eq_card_field K hK SB]
  have hcardH : Nat.card ↥((Usub K).prod (Usub K)) = Nat.card K * Nat.card K := by
    rw [Nat.card_congr (Subgroup.prodEquiv (Usub K) (Usub K)).toEquiv, Nat.card_prod,
      card_Usub]
  refine (Subgroup.eq_of_le_of_card_ge hT ?_).symm
  exact le_of_eq (hcardT.trans hcardH.symm)

theorem normalizer_prod_Usub_eq [CharP K 2] :
    Subgroup.normalizer
        (((Usub K).prod (Usub K) : Subgroup (SL2 K × SL2 K)) : Set (SL2 K × SL2 K)) =
      (Bsub K).prod (Bsub K) := by
  rw [normalizer_prod_eq (Usub K) (Usub K), normalizer_Usub_eq_Bsub]

theorem prod_top_bot_le_or_of_prod_Bsub_le [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {P : Subgroup (SL2 K × SL2 K)} (hP : (Bsub K).prod (Bsub K) ≤ P)
    (hne : ¬ P ≤ (Bsub K).prod (Bsub K)) :
    (⊤ : Subgroup (SL2 K)).prod (⊥ : Subgroup (SL2 K)) ≤ P ∨
      (⊥ : Subgroup (SL2 K)).prod (⊤ : Subgroup (SL2 K)) ≤ P := by
  let QA : Subgroup (SL2 K) := P.map (MonoidHom.fst (SL2 K) (SL2 K))
  let QB : Subgroup (SL2 K) := P.map (MonoidHom.snd (SL2 K) (SL2 K))
  have hB_le_QA : Bsub K ≤ QA := by
    intro x hx
    have hmem : (x, 1) ∈ (Bsub K).prod (Bsub K) :=
      Subgroup.mem_prod.mpr ⟨hx, Subgroup.one_mem _⟩
    exact Subgroup.mem_map_of_mem (MonoidHom.fst (SL2 K) (SL2 K)) (hP hmem)
  have hB_le_QB : Bsub K ≤ QB := by
    intro x hx
    have hmem : (1, x) ∈ (Bsub K).prod (Bsub K) :=
      Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, hx⟩
    exact Subgroup.mem_map_of_mem (MonoidHom.snd (SL2 K) (SL2 K)) (hP hmem)
  have hQA : QA ≤ Bsub K ∨ QA = ⊤ :=
    borel_or_top (K := K) (H := QA) (fun t => hB_le_QA (uU_mem_Bsub t))
  have hQB : QB ≤ Bsub K ∨ QB = ⊤ :=
    borel_or_top (K := K) (H := QB) (fun t => hB_le_QB (uU_mem_Bsub t))
  rcases hQA with hQA | hQA <;> rcases hQB with hQB | hQB
  · exact absurd (fun x hx => Subgroup.mem_prod.mpr
      ⟨hQA (Subgroup.mem_map_of_mem (MonoidHom.fst (SL2 K) (SL2 K)) hx),
       hQB (Subgroup.mem_map_of_mem (MonoidHom.snd (SL2 K) (SL2 K)) hx)⟩) hne
  · exact Or.inr (secondFactor_le_of_proj_eq_top_of_fst_le P (Bsub K) (Bsub K) hP hQB hQA)
  · exact Or.inl (firstFactor_le_of_proj_eq_top_of_snd_le P (Bsub K) (Bsub K) hP hQA hQB)
  · exact Or.inl (firstFactor_le_of_proj_eq_top P (Bsub K) (Bsub K) hP hQA hQB
      (commutator_top_Bsub K hK))

theorem commutator_prod_top_bot_SL2 [Finite K] (hK : 4 ≤ Nat.card K) :
    ⁅(⊤ : Subgroup (SL2 K)).prod (⊥ : Subgroup (SL2 K)),
        (⊤ : Subgroup (SL2 K)).prod (⊥ : Subgroup (SL2 K))⁆ =
      (⊤ : Subgroup (SL2 K)).prod (⊥ : Subgroup (SL2 K)) := by
  have htop : ⁅(⊤ : Subgroup (SL2 K)), (⊤ : Subgroup (SL2 K))⁆ = ⊤ := by
    rw [← commutator_def]
    exact Group.isPerfect_def.mp
      (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK)
  rw [Subgroup.commutator_prod_prod, Subgroup.commutator_bot_right, htop]

theorem commutator_prod_bot_top_SL2 [Finite K] (hK : 4 ≤ Nat.card K) :
    ⁅(⊥ : Subgroup (SL2 K)).prod (⊤ : Subgroup (SL2 K)),
        (⊥ : Subgroup (SL2 K)).prod (⊤ : Subgroup (SL2 K))⁆ =
      (⊥ : Subgroup (SL2 K)).prod (⊤ : Subgroup (SL2 K)) := by
  have htop : ⁅(⊤ : Subgroup (SL2 K)), (⊤ : Subgroup (SL2 K))⁆ = ⊤ := by
    rw [← commutator_def]
    exact Group.isPerfect_def.mp
      (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK)
  rw [Subgroup.commutator_prod_prod, Subgroup.commutator_bot_left, htop]

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

module

public import CFSG.LieType.Chevalley.RootLocalComponentFree

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open Subgroup CFSG

namespace RootWeightDatum


variable {K : Type} [Field K]

theorem parabolic_univ (D : RootWeightDatum K) : D.parabolic Set.univ = D.group := by
  cases D with
  | ordinary τ => exact (standard_parabolic_cells τ K).2.2.2.2.2.1
  | fixed t σ hσ => exact (fixed_standard_parabolic_cells t K σ).2.2.2.2.2

theorem exists_eq_parabolic_of_borel_le (D : RootWeightDatum K) {A : Subgroup (ModGL D.tag K)}
    (hB : D.borel ≤ A) (hA : A ≤ D.group) : ∃ J : Set (Fin D.rank), A = D.parabolic J := by
  cases D with
  | ordinary τ => exact ⟨_, eq_parabolicSubgroup_of_borelGroup_le hB hA⟩
  | fixed t σ hσ => exact ⟨_, (fixed_Borel_overgroup_classification t K σ A hB hA).1⟩

theorem isCharacteristicP_parabolic [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (D : RootWeightDatum K) {J : Set (Fin D.rank)} (hJ : J ≠ Set.univ) :
    CFSG.IsCharacteristicP p ↥(D.parabolic J) := by
  have hUP : D.radical J ≤ D.parabolic J := D.radical_le_parabolic J
  have hUn : ((D.radical J).subgroupOf (D.parabolic J)).Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact D.conj_mem_radical J x.2 hn
  have hUp : IsPGroup p (D.radical J) := D.isPGroup_radical p J
  have hCU : centralizer (D.radical J : Set (ModGL D.tag K)) ⊓ D.parabolic J ≤ D.radical J := by
    have h := D.parabolic_inf_centralizer_le_radical hJ
    rwa [inf_comm] at h
  have hUcore : (D.radical J).subgroupOf (D.parabolic J) ≤ CFSG.pCore p ↥(D.parabolic J) :=
    le_sSup ⟨hUn, hUp.comap_of_injective _ (D.parabolic J).subtype_injective⟩
  intro x hx
  apply hUcore
  have hxU : (x : ModGL D.tag K) ∈
      centralizer (D.radical J : Set (ModGL D.tag K)) ⊓ D.parabolic J := by
    refine ⟨mem_centralizer_iff.2 fun u hu => ?_, x.2⟩
    exact congrArg Subtype.val
      (mem_centralizer_iff.1 hx ⟨u, hUP hu⟩
        (hUcore (show (⟨u, hUP hu⟩ : ↥(D.parabolic J)) ∈
          (D.radical J).subgroupOf (D.parabolic J) from hu)))
  exact hCU hxU

theorem isCharacteristicP_of_borel_le [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (D : RootWeightDatum K) {A : Subgroup (ModGL D.tag K)} (hB : D.borel ≤ A) (hA : A ≤ D.group)
    (hne : A ≠ D.group) : CFSG.IsCharacteristicP p ↥A := by
  obtain ⟨J, rfl⟩ := D.exists_eq_parabolic_of_borel_le hB hA
  have hJ : J ≠ Set.univ := by
    intro h
    exact hne (by rw [h]; exact D.parabolic_univ)
  exact D.isCharacteristicP_parabolic p hJ

end RootWeightDatum

end CFSG.LieType.Chevalley

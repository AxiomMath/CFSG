module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5Tor
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBE7E8
import CFSG.LieType.Steinberg.CentralExt.FieldTwoMultiplier

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExcTwo TableBExcTwoTB

section Inputs


@[expose] def GGE8TwoTorusNodeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ A : Subgroup (adjointGroup .E8 K), A ≤ (tE K frameE8).range → 3 ^ 7 ≤ Nat.card A →
      ∀ x ∈ A, x ≠ 1 → NodeCount 3 A x

end Inputs

section Assembly


theorem ker_eq_bot_recipe_E8_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (L' : Type) [Group L'] [Finite L'] (ψ : L' →* TableBExc.RecipeGroup .E8 K)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) : ψ.ker = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 1) (by rw [pow_one]; exact hK)
  let qe : TableBExc.RecipeGroup .E8 K ≃* adjointGroup .E8 K := TableBExc.recipeEquiv .E8 K
  have hψ' : Function.Surjective (qe.toMonoidHom.comp ψ) := qe.surjective.comp hψ
  have hker' : (qe.toMonoidHom.comp ψ).ker ≤ Subgroup.center L' := by
    rwa [MonoidHom.ker_comp_of_injective ψ qe.toMonoidHom qe.injective]
  obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.FieldTwo.e8_two_exists_section
      (K := K) hK L' (qe.toMonoidHom.comp ψ) hψ' hker'
  haveI : Group.IsPerfect L' := ⟨hperf⟩
  have hbot := CFSG.SectionRank.ker_eq_bot_of_section_of_perfect _ hker' σ hσ
  rwa [MonoidHom.ker_comp_of_injective ψ qe.toMonoidHom qe.injective] at hbot

theorem ggE8TwoNormSmallInput_of_nodes
    (hSC : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → GGE8TwoSCToral K)
    (hN : GGE8TwoTorusNodeInput) : GGE8TwoNormSmallInput := by
  intro K _ _ hK
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 1) (by rw [pow_one]; exact hK)
  haveI : Finite (adjointGroup .E8 K) := generated_group_finite .E8 K
  refine ggStdSubTwoTorusNormSmall_of_count (G0 := adjointGroup .E8 K)
    (TableBExc.recipeEquiv .E8 K) center_adjointGroup_eq_bot ?_
    (fun L' _ _ ψ hψ hker hperf => ker_eq_bot_recipe_E8_two hK L' ψ hψ hker hperf) ?_
  · intro φ hφ
    obtain ⟨r, rfl⟩ := TableBExc.idImage_subset_inn_E8 K hφ
    refine ⟨TableBExc.recipeEquiv .E8 K r, ?_⟩
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  · exact hcount_of_toral (T := (tE K frameE8).range) (hSC K hK) (hN K hK)

end Assembly

end CFSG.StandardType.SmallExc

end

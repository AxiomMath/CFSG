module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6Nodes
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5Norm
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  TableBExc.E6Three E6TwoPilot

section Assembly


theorem ker_eq_bot_recipe_E6_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (L' : Type) [Group L'] [Finite L'] (ψ : L' →* TableBExc.RecipeGroup .E6 K)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) : ψ.ker = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 1) (by rw [pow_one]; exact hK)
  have hfinj : Function.Injective (CFSG.LieType.Steinberg.Isogeny.e6Isogeny K) :=
    CFSG.LieType.Steinberg.CentralExt.FieldTwo.e6Isogeny_injective_two (K := K) hK
  have hfsurj : Function.Surjective (CFSG.LieType.Steinberg.Isogeny.e6Isogeny K) :=
    CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective K
  let qe : ↥((CFSG.LieType.Steinberg.Minuscule.e6Data_valid).minGroup K) ≃*
      TableBExc.RecipeGroup .E6 K :=
    (MulEquiv.ofBijective (CFSG.LieType.Steinberg.Isogeny.e6Isogeny K) ⟨hfinj, hfsurj⟩).trans
      (TableBExc.recipeEquiv .E6 K).symm
  have hψ' : Function.Surjective (qe.symm.toMonoidHom.comp ψ) := qe.symm.surjective.comp hψ
  have hker' : (qe.symm.toMonoidHom.comp ψ).ker ≤ Subgroup.center L' := by
    rwa [MonoidHom.ker_comp_of_injective ψ qe.symm.toMonoidHom qe.symm.injective]
  obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.FieldTwo.e6_two_exists_section
      (K := K) hK L' (qe.symm.toMonoidHom.comp ψ) hψ' hker'
  haveI : Group.IsPerfect L' := ⟨hperf⟩
  have hbot := CFSG.SectionRank.ker_eq_bot_of_section_of_perfect _ hker' σ hσ
  rwa [MonoidHom.ker_comp_of_injective ψ qe.symm.toMonoidHom qe.symm.injective] at hbot

theorem ggE6TwoNormSmallInput_of_nodes (hD4 : GGE6TwoD4NodeInput) (hIso : GGE6TwoIsoNodeInput) :
    GGE6TwoNormSmallInput := by
  intro K _ _ hK
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 1) (by rw [pow_one]; exact hK)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  haveI : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  refine ggStdSubTwoTorusNormSmall_of_count (G0 := adjointGroup .E6 K)
    (TableBExc.recipeEquiv .E6 K) center_adjointGroup_eq_bot ?_
    (fun L' _ _ ψ hψ hker hperf => ker_eq_bot_recipe_E6_two hK L' ψ hψ hker hperf) ?_
  · intro φ hφ
    obtain ⟨r, rfl⟩ := recipeID_subset_inn_E6_two hK hφ
    refine ⟨TableBExc.recipeEquiv .E6 K r, ?_⟩
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  · intro B hB hcard _ x hx hx1
    obtain ⟨c, hc⟩ := exists_conj_eq_range_torusE6Two h2 hK hB hcard
    refine nodeCount_of_map (MulAut.conj c) ?_
    rw [hc]
    obtain ⟨w, hw⟩ : (MulAut.conj c) x ∈ (torusE6Two (K := K) h2).range := by
      rw [← hc]
      exact ⟨x, hx, rfl⟩
    have hw0 : Multiplicative.toAdd w ≠ 0 := by
      intro h0
      apply hx1
      have hw1 : w = 1 := by
        rw [← ofAdd_toAdd w, h0]
        rfl
      rw [hw1, map_one] at hw
      exact (MulAut.conj c).injective (hw.symm.trans (map_one _).symm)
    rw [← hw, ← ofAdd_toAdd w]
    exact nodeCount_torusE6Two hD4 hIso h2 hK hw0

end Assembly

end CFSG.StandardType.SmallExc

end

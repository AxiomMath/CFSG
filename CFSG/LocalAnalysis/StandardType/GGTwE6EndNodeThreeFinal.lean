module

public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeLocal
public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeAssembly
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6RankFive
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeEnd
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeEndLift
import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.TwE6D3
  CFSG.StandardType.TwE6RootAs CFSG.StandardType.TwE6RootKill

section Final


theorem ggTwE6EndNodeThreeRankFour_of_inputs (hRK : RootKill)
    (hD34 : TwE6FieldCore.SubfieldLangDatumThreeFour) (hGen : TwE6CorootCoreGen)
    (hOut : TwE6OuterRankFour) : GGTwE6EndNodeThreeRankFour := by
  intro K _ _ n p hn hK hp hpq hp3
  subst hp3
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hlt hadm
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  rw [TwE6Delta.liftRank_three] at hr hlt
  have hAc : Nat.card A = 3 ^ 4 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.Open.IsElemAbelian.isPGroup hA)
    rw [hk] at hr hlt ⊢
    have h1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hr
    have h2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 hlt
    rw [show k = 4 by omega]
  obtain ⟨U, hU1, hU2, hAN⟩ : ∃ U : Subgroup (MulAut L'), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      A ≤ Subgroup.normalizer (U : Set (MulAut L')) := by
    have hcov := ggTwE6CoverRank_recipe hn hK hpq L' ψ hψ hker hperf
    rcases hadm with hα | ⟨-, hδ⟩ | ⟨hZ3, hδ⟩
    · exact hα
    · obtain ⟨E, hE, hE5⟩ := hcov.1
      have h := hδ E hE
      rw [hAc] at h
      omega
    · obtain ⟨E, hE, hE6⟩ := hcov.2 hZ3
      have h := hδ E hE
      rw [hAc] at h
      omega
  have hinj : Function.Injective (iterateFrobenius K 2 n) := (iterateFrobenius K 2 n).injective
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 n)
    ⟨hinj, Finite.surjective_of_injective hinj⟩ with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  set ψ' : L' →* ↥(twistedE6RootGroup K σ) := ε.symm.toMonoidHom.comp ψ with hψ'def
  have hψ'ψ : ∀ l, ψ' l = ε.symm (ψ l) := fun l => rfl
  have hψ' : Function.Surjective ψ' := ε.symm.surjective.comp hψ
  have hZ' : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hker' : ψ'.ker ≤ Subgroup.center L' := fun x hx => hker (by
    have h : ε.symm (ψ x) = 1 := hx
    exact (map_eq_one_iff _ ε.symm.injective).1 h)
  have hρinj : Function.Injective (ggIE_indAutHom hψ' hZ' hker') :=
    ggIE_indAutHom_injective hψ' hZ' hker' hperf
  have hiff := rho_mem_range_twConj_iff hε hψ'ψ hψ' hZ' hker'
  have hY : IsElemAbelian 3 (A.map (ggIE_indAutHom hψ' hZ' hker')) :=
    ggIE_isElemAbelian_map _ hA
  have hYc : Nat.card (A.map (ggIE_indAutHom hψ' hZ' hker')) = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective hρinj]
    exact hAc
  have hYI : A.map (ggIE_indAutHom hψ' hZ' hker') ≤ (RecipeExcLang.twConj K σ).range := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hiff y).1 (hAI y hy)
  have hV1 : U.map (ggIE_indAutHom hψ' hZ' hker') ≠ ⊥ := fun h =>
    hU1 ((Subgroup.map_eq_bot_iff_of_injective U hρinj).1 h)
  have hV2 : IsPGroup 2 (U.map (ggIE_indAutHom hψ' hZ' hker')) := hU2.map _
  have hYV : ∀ y ∈ A.map (ggIE_indAutHom hψ' hZ' hker'),
      ∀ v ∈ U.map (ggIE_indAutHom hψ' hZ' hker'),
        y * v * y⁻¹ ∈ U.map (ggIE_indAutHom hψ' hZ' hker') := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨u, hu, rfl⟩
    exact ⟨a * u * a⁻¹, (Subgroup.mem_set_normalizer_iff.1 (hAN ha) u).1 hu, by simp⟩
  obtain ⟨τ, hτA, hτ1, X, D, hfix, hXc, hXD, hDq, h7, hcent⟩ :=
    TwE6EndNode3.exists_coroot_data_of_two_local hRK hD34 hGen hOut hn hK σ hσ hpq hZ'
      (fun φ hφ k hk => TwE6EndNode3.mem_range_conj_of_two_pow σ hn hK hε hφ hk)
      hY hYI hYc hV1 hV2 hYV
  obtain ⟨t, htA, rfl⟩ := hτA
  have ht1 : t ≠ 1 := fun h => hτ1 (by rw [h, map_one])
  have hcent' : ∀ y ∈ A, (∀ x ∈ D, ggIE_indAutHom hψ' hZ' hker' y x = x) →
      ∃ x ∈ X, ggIE_indAutHom hψ' hZ' hker' y = MulAut.conj x := fun y hy hyD =>
    hcent _ ⟨y, hy, rfl⟩ hyD
  obtain ⟨hend, -⟩ := endNode_of_data hψ' hZ' hker' hperf hA htA ht1 hfix hXc hXD hDq h7 hcent'
  exact ⟨t, hend.1, hend.2.1, hend.2.2.1, hend.2.2.2⟩

theorem ggTwE6EndNodeThreeInput_of_inputs (hRK : RootKill)
    (hD34 : TwE6FieldCore.SubfieldLangDatumThreeFour) (hGen : TwE6CorootCoreGen)
    (hOut : TwE6OuterRankFour) : GGTwE6EndNodeThreeInput :=
  ggTwE6EndNodeThreeInput_of_rankFour (twE6CorootCore_of_gen hGen)
    (ggTwE6EndNodeThreeRankFour_of_inputs hRK hD34 hGen hOut)

theorem ggTwE6EndNodeThreeInput_of_upgrade (hRK : RootKill)
    (hD34 : TwE6FieldCore.SubfieldLangDatumThreeFour) (hCore : TwE6CorootCore)
    (hU : TwE6EnnolaUpgrade) (hOut : TwE6OuterRankFour) : GGTwE6EndNodeThreeInput :=
  ggTwE6EndNodeThreeInput_of_inputs hRK hD34 (twE6CorootCoreGen_of_upgrade hU hCore) hOut

end Final

end CFSG.StandardType

end

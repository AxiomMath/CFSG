module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldHCore
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Dvd
public import CFSG.LocalAnalysis.StandardType.GGTwE6LeviSplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaSplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillWeyl

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.TwE6RootKill CFSG.StandardType.TwE6Transport

section Core


theorem ggTwE6FieldCentInvInput_of_core (hRK : RootKill) (h5 : SubfieldLangDatumFive)
    (h3 : SubfieldLangDatumThree) (h34 : SubfieldLangDatumThreeFour) :
    GGTwE6FieldCentInvInput := by
  intro K _ _ n p hn hK hp hpq hp3 _ f hf hord A B hA _ hfix hBA hB5 ⟨V, hV1, hV2, hVB⟩
  haveI : CharP K 2 := charP_two_of_card_sq hK
  obtain ⟨σ, hσ⟩ : ∃ σ : K ≃+* K, ∀ c, σ c = c ^ 2 ^ n :=
    ⟨iterateFrobeniusEquiv K 2 n, fun c => by
      rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]⟩
  obtain ⟨ε, -, hfD⟩ := exists_recipeConj_field hn hK σ hσ
  obtain ⟨δ, rfl⟩ := hfD f hf
  have hδ : orderOf δ = p :=
    (orderOf_fieldActor hn hK hσ δ).symm.trans ((MulEquiv.orderOf_eq _ _).symm.trans hord)
  have hBN : B ≤ Subgroup.normalizer (V : Set (TwE6Delta.RecipeR K n)) := fun b hb =>
    Subgroup.mem_normalizer_iff.2 fun v => ⟨hVB b hb v, fun hv => by
      have h1 := hVB b⁻¹ (inv_mem hb) _ hv
      rwa [show b⁻¹ * (b * v * b⁻¹) * b⁻¹⁻¹ = v by group] at h1⟩
  have hXδ : ∀ x ∈ eltMat σ ε B, Units.map (entrywiseHom δ.toRingHom) x = x := fun x hx => by
    obtain ⟨hx0, hxB⟩ := (mem_eltMat σ ε).1 hx
    have h1 : ε (fieldActor σ δ (ε.symm (ε ⟨x, hx0⟩))) = ε ⟨x, hx0⟩ := hfix _ (hBA hxB)
    rw [MulEquiv.symm_apply_apply] at h1
    exact congrArg Subtype.val (ε.injective h1)
  have hr : p ^ (if p = 3 then 4 else 5) ≤ Nat.card (eltMat σ ε B) :=
    le_of_eq (by rw [if_neg hp3, card_eltMat, hB5])
  obtain ⟨u, hu, hu1, ⟨k, hk⟩, hδu, hcomm⟩ := exists_fixed_two_of_entrywise hRK h5 h3 h34 hn hK
    hσ hp hpq δ hδ (eltMat_le σ ε B) (isElemAbelian_eltMat σ ε (hA.mono hBA)) hr hXδ
    (twNormTwo_eltMat σ ε hV1 hV2 hBN)
  have hfv : MulAut.congr ε (fieldActor σ δ) (ε ⟨u, hu⟩) = ε ⟨u, hu⟩ := by
    show ε (fieldActor σ δ (ε.symm (ε ⟨u, hu⟩))) = ε ⟨u, hu⟩
    rw [MulEquiv.symm_apply_apply]
    exact congrArg ε (Subtype.ext hδu)
  have h2 : ε ⟨u, hu⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow ε, map_eq_one_iff ε ε.injective]
    exact Subtype.ext ((SubgroupClass.coe_pow _ _).trans hk)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h2)
  rcases m with _ | j
  · have h1 : ε ⟨u, hu⟩ = 1 := orderOf_eq_one_iff.1 (by rw [hm, pow_zero])
    exact absurd (congrArg Subtype.val ((map_eq_one_iff ε ε.injective).1 h1)) hu1
  have hw : orderOf (ε ⟨u, hu⟩ ^ 2 ^ j) = 2 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero j two_ne_zero) (by rw [hm]; exact pow_dvd_pow 2 j.le_succ),
      hm, pow_succ, Nat.mul_div_cancel_left _ (pow_pos two_pos j)]
  have hw2 := pow_orderOf_eq_one (ε ⟨u, hu⟩ ^ 2 ^ j)
  rw [hw] at hw2
  refine ⟨ε ⟨u, hu⟩ ^ 2 ^ j, fun h => ?_, hw2, by rw [map_pow, hfv],
    fun b hb => ((commute_of_forall_commute_eltMat σ ε hu hcomm hb).pow_left _).eq.symm⟩
  rw [h, orderOf_one] at hw
  exact absurd hw (by norm_num)

end Core


theorem ggTwE6FieldCentInvInput_of_langDatum (h5 : SubfieldLangDatumFive)
    (h3 : SubfieldLangDatumThree) (h34 : SubfieldLangDatumThreeFour) :
    GGTwE6FieldCentInvInput :=
  ggTwE6FieldCentInvInput_of_core (rootKill_of_ennolaKill_weylKill
      (ennolaKill_of_steps leviSplitStep_holds ennolaSplitStep_holds) weylKill_holds) h5 h3 h34

end CFSG.StandardType.TwE6FieldCore

end

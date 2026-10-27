module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldFixed
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldCore

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.TwE6RootKill CFSG.StandardType.TwE6Transport


theorem ggTwE6FieldHCore_of_core (hRK : RootKill) (h5 : SubfieldLangDatumFive)
    (h3 : SubfieldLangDatumThree) (h34 : SubfieldLangDatumThreeFour) {K : Type} [Field K]
    [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {p r : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hr : TwE6Delta.liftRank p ≤ r) :
    ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n),
      orderOf f = p → ∀ Y : Subgroup (MulAut (TwE6Delta.RecipeR K n)), IsElemAbelian p Y →
      (Y : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n →
      p ^ r ≤ Nat.card Y → (∀ φ ∈ Y, φ * f = f * φ) →
      (∃ V : Subgroup (TwE6Delta.RecipeR K n), V ≠ ⊥ ∧ IsPGroup 2 V ∧
        ∀ φ ∈ Y, ∀ v ∈ V, φ v ∈ V) →
      ∃ V : Subgroup (TwE6Delta.RecipeR K n), V ≠ ⊥ ∧ IsPGroup 2 V ∧
        ∀ φ ∈ Y ⊔ Subgroup.zpowers f, ∀ v ∈ V, φ v ∈ V := by
  rintro f hf hord Y hY hYI hYr hYf ⟨V, hV1, hV2, hYV⟩
  haveI : CharP K 2 := charP_two_of_card_sq hK
  obtain ⟨σ, hσ⟩ : ∃ σ : K ≃+* K, ∀ c, σ c = c ^ 2 ^ n :=
    ⟨iterateFrobeniusEquiv K 2 n, fun c => by
      rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]⟩
  obtain ⟨ε, hε, hfD⟩ := exists_recipeConj_field hn hK σ hσ
  obtain ⟨δ, rfl⟩ := hfD f hf
  have hδ : orderOf δ = p :=
    (orderOf_fieldActor hn hK hσ δ).symm.trans ((MulEquiv.orderOf_eq _ _).symm.trans hord)
  have hYc : Y ≤ (recipeConj σ ε).range := fun φ hφ => (hε φ).2 (hYI hφ)
  have hrX : p ^ (if p = 3 then 4 else 5) ≤ Nat.card (recipeMat σ ε Y) := by
    rw [card_recipeMat σ ε hn hK hσ hYc]
    exact (Nat.pow_le_pow_right hp.pos hr).trans hYr
  obtain ⟨u, hu, hu1, ⟨k, hk⟩, hδu, hcomm⟩ := exists_fixed_two_of_entrywise hRK h5 h3 h34 hn hK
    hσ hp hpq δ hδ (recipeMat_le σ ε Y) (isElemAbelian_recipeMat σ ε hn hK hσ hY) hrX
    (fun x hx => entrywise_eq_of_mem_recipeMat hn hK hσ ε hYf hx)
    (twNormTwo_recipeMat σ ε hV1 hV2 hYV)
  have hfu : MulAut.congr ε (fieldActor σ δ) (ε ⟨u, hu⟩) = ε ⟨u, hu⟩ := by
    show ε (fieldActor σ δ (ε.symm (ε ⟨u, hu⟩))) = ε ⟨u, hu⟩
    rw [MulEquiv.symm_apply_apply]
    exact congrArg ε (Subtype.ext hδu)
  have hst : Y ⊔ Subgroup.zpowers (MulAut.congr ε (fieldActor σ δ)) ≤
      MulAction.stabilizer (MulAut (TwE6Delta.RecipeR K n)) (ε ⟨u, hu⟩) :=
    sup_le (fun φ hφ => MulAction.mem_stabilizer_iff.2
        (apply_eq_of_forall_commute_recipeMat σ ε hYc hu hcomm hφ))
      (Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hfu))
  have h2 : ε ⟨u, hu⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow ε, map_eq_one_iff ε ε.injective]
    exact Subtype.ext ((SubgroupClass.coe_pow _ _).trans hk)
  refine ⟨Subgroup.zpowers (ε ⟨u, hu⟩), Subgroup.zpowers_ne_bot.2 fun h => hu1
    (congrArg Subtype.val ((map_eq_one_iff ε ε.injective).1 h)), ?_, fun φ hφ v hv => ?_⟩
  · rintro ⟨w, hw⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    have hφu : φ (ε ⟨u, hu⟩) = ε ⟨u, hu⟩ := MulAction.mem_stabilizer_iff.1 (hst hφ)
    rw [map_zpow, hφu]
    exact Subgroup.zpow_mem_zpowers _ m

end CFSG.StandardType.TwE6FieldCore

end

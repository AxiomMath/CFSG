module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcOut
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

private theorem a3e7_ofAdd_pow_three {n : ℕ} (x : Multiplicative (Fin n → ZMod 3)) :
    x ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  show (3 : ℕ) • Multiplicative.toAdd x = 0
  funext i
  simp only [Pi.smul_apply, Pi.zero_apply]
  rw [← Nat.cast_smul_eq_nsmul (ZMod 3) 3, CharP.cast_eq_zero (ZMod 3) 3, zero_smul]

private theorem a3e7_zpowers_ne_bot_isPGroup_two {P : Type*} [Group P] {g : P} (hg1 : g ≠ 1)
    (hg2 : g ^ 2 = 1) : Subgroup.zpowers g ≠ ⊥ ∧ IsPGroup 2 (Subgroup.zpowers g) := by
  refine ⟨by rw [Ne, Subgroup.zpowers_eq_bot]; exact hg1, ?_⟩
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, orderOf_eq_prime hg2 hg1, pow_one]

private theorem a3e7_mem_normalizer_zpowers_of_commute {P : Type*} [Group P] {g h : P}
    (hgh : Commute h g) :
    h ∈ Subgroup.normalizer (Subgroup.zpowers g : Set P) := by
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu => ?_)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  exact (hgh.zpow_right k).eq.symm

private theorem a3e7_model
    {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ U E : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .E7 K),
      U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set _) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : TableBExcTwo.OrthFrame .E7 6 := TableBExcTwo.frameE7
  let U₀ : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .E7 K) :=
    Subgroup.zpowers (TableBExcTwo.rootInv K F)
  let E₀ : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .E7 K) :=
    (TableBExcTwo.torusE K F).range
  have hU₀ : U₀ ≠ ⊥ :=
    (a3e7_zpowers_ne_bot_isPGroup_two (TableBExcTwo.rootInv_ne_one F)
      (TableBExcTwo.rootInv_sq F)).1
  have hU₂ : IsPGroup 2 U₀ :=
    (a3e7_zpowers_ne_bot_isPGroup_two (TableBExcTwo.rootInv_ne_one F)
      (TableBExcTwo.rootInv_sq F)).2
  have hEab : IsElemAbelian 3 E₀ := by
    change IsElemAbelian 3 (TableBExcTwo.torusE K F).range
    have htop : IsElemAbelian 3 (⊤ : Subgroup (Multiplicative (Fin 6 → ZMod 3))) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => ?_⟩
      · exact Subtype.ext (mul_comm (a : Multiplicative (Fin 6 → ZMod 3)) b)
      · exact a3e7_ofAdd_pow_three x
    have h := CFSG.Open.IsElemAbelian.map htop (TableBExcTwo.torusE K F)
    rwa [Subgroup.map_top] at h
  have hEcard : Nat.card E₀ = 3 ^ 6 := by
    change Nat.card (TableBExcTwo.torusE K F).range = 3 ^ 6
    rw [← Nat.card_congr
        (MonoidHom.ofInjective (TableBExcTwo.torusE_injective F)).toEquiv,
      Nat.card_congr (MulEquiv.piMultiplicative fun _ : Fin 6 => ZMod 3).toEquiv,
      Nat.card_fun,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3),
      Nat.card_zmod, Nat.card_fin]
  have hEU : E₀ ≤ Subgroup.normalizer (U₀ : Set _) := by
    intro x hx
    change x ∈ (TableBExcTwo.torusE K F).range at hx
    obtain ⟨v, rfl⟩ := hx
    change TableBExcTwo.torusE K F v ∈
      Subgroup.normalizer (Subgroup.zpowers (TableBExcTwo.rootInv K F) : Set _)
    exact a3e7_mem_normalizer_zpowers_of_commute (TableBExcTwo.torusE_commute_rootInv F v)
  exact ⟨U₀, E₀, hU₀, hU₂, hEU, hEab, hEcard⟩

private theorem a3e7_transport {G A : Type} [Group G] [Group A] {K : Subgroup G} (φ : K ≃* A)
    {U₀ E₀ : Subgroup A} (hU₀ : U₀ ≠ ⊥) (hU₂ : IsPGroup 2 U₀)
    (hE₀U₀ : E₀ ≤ Subgroup.normalizer (U₀ : Set A)) (hEab : IsElemAbelian 3 E₀)
    (hEcard : Nat.card E₀ = 3 ^ 6) :
    ∃ U E : Subgroup G, U ≤ K ∧ E ≤ K ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set G) ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 6 := by
  let UK : Subgroup K := U₀.comap φ.toMonoidHom
  let EK : Subgroup K := E₀.comap φ.toMonoidHom
  have hmapU : UK.map φ.toMonoidHom = U₀ := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr φ.surjective, top_inf_eq]
  have hmapE : EK.map φ.toMonoidHom = E₀ := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr φ.surjective, top_inf_eq]
  have hUK2 : IsPGroup 2 UK := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    obtain ⟨n, hn⟩ := isPGroup_iff_pow_pow_eq_one.mp hU₂ ⟨φ (x : K), x.2⟩
    refine ⟨n, Subtype.ext ?_⟩
    refine φ.injective ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one]
    exact congrArg Subtype.val hn
  have hEKab : IsElemAbelian 3 EK := by
    change IsElemAbelian 3 (E₀.comap φ.toMonoidHom)
    have heq : E₀.comap φ.toMonoidHom = E₀.map φ.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm φ E₀
    rw [heq]
    exact TableB.isElemAbelian_map hEab φ.symm.toMonoidHom
  have hnormK : EK ≤ Subgroup.normalizer (UK : Set K) := by
    have h1 : EK ≤ (Subgroup.normalizer (U₀ : Set A)).comap φ.toMonoidHom :=
      fun e he => hE₀U₀ he
    exact h1.trans (Subgroup.le_normalizer_comap φ.toMonoidHom)
  have hUbot : (UK.map K.subtype) ≠ ⊥ := by
    intro h
    have hUK : UK = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hmem : K.subtype x ∈ UK.map K.subtype := ⟨x, hx, rfl⟩
      rw [h] at hmem
      simpa using hmem
    apply hU₀
    rw [← hmapU, hUK, Subgroup.map_bot]
  have hEU : EK.map K.subtype ≤ Subgroup.normalizer (UK.map K.subtype : Set G) :=
    (Subgroup.map_mono hnormK).trans (Subgroup.le_normalizer_map K.subtype)
  refine ⟨UK.map K.subtype, EK.map K.subtype, Subgroup.map_subtype_le _, Subgroup.map_subtype_le _,
    hUbot, hUK2.map K.subtype, hEU, TableB.isElemAbelian_map hEKab K.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective]
  have hcardEK : Nat.card EK = Nat.card E₀ := by
    rw [← hmapE]
    exact (Subgroup.card_map_of_injective φ.injective).symm
  rw [hcardEK, hEcard]

theorem exists_twoLocal_three_of_E7
    {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hz : Subgroup.center K = ⊥)
    (hmark : LargeEvenMarking K fun lab _ _ _ _ _ => lab.tag = .E7 ∧ lab.rank = 0 ∧ lab.n = 1) :
    ∃ U E : Subgroup G, U ≤ K ∧ E ≤ K ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set G) ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 6 := by
  unfold CFSG.StandardType.LargeEvenMarking CFSG.Assembly.LargeEvenMarkingLegacy at hmark
  obtain ⟨-, lab, hlab, hraw⟩ := hmark
  obtain ⟨R₀, hR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨θ₀, hP₀⟩ := hQ₀.2.2
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hP₀
  obtain ⟨ht, hl, hn⟩ := hP₀
  subst ht; subst hl; subst hn
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨K', hKfield, hKfin, hcard, hQ⟩ := hraw
  letI : Field K' := hKfield
  letI : Finite K' := hKfin
  have hK2 : Nat.card K' = 2 := by rw [hcard]; norm_num
  haveI : CharP K' 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two le_rfl (by rw [pow_one]; exact hK2)
  obtain ⟨θ, -⟩ := hQ.2.2
  let e : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K' false) ≃*
      ↥(CFSG.Blueprint.Chevalley.adjointGroup .E7 K') := recipeChevEquiv .E7 K'
  let e0 : (K ⧸ Subgroup.center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  let φ : K ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup .E7 K') := e0.symm.trans (θ.trans e)
  obtain ⟨U₀, E₀, hU₀, hU₂, hE₀, hEab, hEcard⟩ := a3e7_model (K := K')
  exact a3e7_transport φ hU₀ hU₂ hE₀ hEab hEcard

end CFSG.StandardType.FrameRoute

end

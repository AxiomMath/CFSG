module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIKit
public import CFSG.RankThree.PartTwo.KFacts.K71G2
public import CFSG.Quasithin.Background.G2UAdjoint
import CFSG.LocalAnalysis.SectionRank.ExceptionalEvenCover
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.G2U
open KFacts

namespace Item434SmallTwoIII

theorem coe_gen0 : ((gen0 : GL (Fin 14) (ZMod 2)) : Matrix (Fin 14) (Fin 14) (ZMod 2)) =
    dec2 g0c := rfl

theorem coe_gen1 : ((gen1 : GL (Fin 14) (ZMod 2)) : Matrix (Fin 14) (Fin 14) (ZMod 2)) =
    dec2 g1c := rfl

theorem coe_gen2 : ((gen2 : GL (Fin 14) (ZMod 2)) : Matrix (Fin 14) (Fin 14) (ZMod 2)) =
    dec2 g2c := rfl

theorem coe_gen3 : ((gen3 : GL (Fin 14) (ZMod 2)) : Matrix (Fin 14) (Fin 14) (ZMod 2)) =
    dec2 g3c := rfl

@[expose] def g2a : GL (Fin 14) (ZMod 2) := gen1 * gen3

@[expose] def g2b : GL (Fin 14) (ZMod 2) :=
  gen0 * gen1 * gen0 * gen1 * gen2 * gen3 * gen1 * gen0 * gen2 * gen3 * gen1 * gen2

@[expose] def g2aC : List ℕ := mul2 g1c g3c

@[expose] def g2bC : List ℕ :=
  mul2 (mul2 (mul2 (mul2 (mul2 (mul2 (mul2 (mul2 (mul2 (mul2 (mul2 g0c g1c) g0c) g1c) g2c)
    g3c) g1c) g0c) g2c) g3c) g1c) g2c

theorem coe_g2a : ((g2a : GL (Fin 14) (ZMod 2)) : Matrix (Fin 14) (Fin 14) (ZMod 2)) =
    dec2 g2aC := by
  simp only [g2a, g2aC, Units.val_mul, dec2_mul2, coe_gen1, coe_gen3]

theorem coe_g2b : ((g2b : GL (Fin 14) (ZMod 2)) : Matrix (Fin 14) (Fin 14) (ZMod 2)) =
    dec2 g2bC := by
  simp only [g2b, g2bC, Units.val_mul, dec2_mul2, coe_gen0, coe_gen1, coe_gen2, coe_gen3]

theorem g2ab_codes : mul2 (mul2 g2aC g2aC) g2aC = id2 ∧ mul2 (mul2 g2bC g2bC) g2bC = id2 ∧
    mul2 g2aC g2bC = mul2 g2bC g2aC ∧ g2bC ≠ id2 ∧ g2bC ≠ g2aC ∧ g2bC ≠ mul2 g2aC g2aC ∧
    g2aC ≠ id2 ∧ canon2 g2bC = true ∧ canon2 id2 = true ∧ canon2 g2aC = true ∧
    canon2 (mul2 g2aC g2aC) = true := by
  decide +kernel

theorem g2a_pow_three : g2a ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_g2a, pow_three', ← dec2_mul2, ← dec2_mul2, g2ab_codes.1,
    dec2_id2, Units.val_one]

theorem g2b_pow_three : g2b ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_g2b, pow_three', ← dec2_mul2, ← dec2_mul2, g2ab_codes.2.1,
    dec2_id2, Units.val_one]

theorem g2a_mul_g2b : g2a * g2b = g2b * g2a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_g2a, coe_g2b, ← dec2_mul2, ← dec2_mul2,
    g2ab_codes.2.2.1]

theorem g2a_ne_one : g2a ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, ha1, -, ci, ca, -⟩ := g2ab_codes
  intro h
  have h1 := congrArg (fun u : GL (Fin 14) (ZMod 2) => (u : Matrix (Fin 14) (Fin 14) (ZMod 2))) h
  simp only [coe_g2a, Units.val_one] at h1
  rw [← dec2_id2] at h1
  exact ha1 (dec2_injective ca ci h1)

theorem orderOf_g2a : orderOf g2a = 3 :=
  orderOf_eq_prime g2a_pow_three g2a_ne_one

theorem g2b_not_mem_zpowers : g2b ∉ Subgroup.zpowers g2a := by
  obtain ⟨-, -, -, h1, ha, ha2, -, cb, ci, ca, ca2⟩ := g2ab_codes
  intro hb
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hk3 : g2a ^ ((k : ZMod 3).val) = g2b := by
    rw [← zpow_natCast, ZMod.val_intCast, ← hk]
    have h3 := zpow_mod_orderOf g2a k
    rw [orderOf_g2a] at h3
    exact h3
  have hval := congrArg (fun u : GL (Fin 14) (ZMod 2) => (u : Matrix (Fin 14) (Fin 14) (ZMod 2)))
    hk3
  simp only [Units.val_pow_eq_pow_val, coe_g2a, coe_g2b] at hval
  have hlt := ZMod.val_lt (k : ZMod 3)
  interval_cases hv : (k : ZMod 3).val
  · rw [pow_zero, ← dec2_id2] at hval
    exact h1 (dec2_injective cb ci hval.symm)
  · rw [pow_one] at hval
    exact ha (dec2_injective cb ca hval.symm)
  · rw [pow_two, ← dec2_mul2] at hval
    exact ha2 (dec2_injective cb ca2 hval.symm)

theorem g2a_mem_rootGroup : g2a ∈ rootGroup :=
  mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem g2b_mem_rootGroup : g2b ∈ rootGroup := by
  have h0 : gen0 ∈ rootGroup := Subgroup.subset_closure (by simp)
  have h1 : gen1 ∈ rootGroup := Subgroup.subset_closure (by simp)
  have h2 : gen2 ∈ rootGroup := Subgroup.subset_closure (by simp)
  have h3 : gen3 ∈ rootGroup := Subgroup.subset_closure (by simp)
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (mul_mem (mul_mem h0 h1) h0) h1) h2) h3) h1) h0) h2) h3) h1) h2

theorem exists_E9_rootGroup : CFSG.Assembly.IsElemAbelian 3
    (Subgroup.zpowers g2a ⊔ Subgroup.zpowers g2b) ∧
    Nat.card (Subgroup.zpowers g2a ⊔ Subgroup.zpowers g2b : Subgroup (GL (Fin 14) (ZMod 2))) =
      9 ∧ Subgroup.zpowers g2a ⊔ Subgroup.zpowers g2b ≤ rootGroup := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers g2a) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, g2a_pow_three, one_zpow]
  have hcomm : ∀ x ∈ Subgroup.zpowers g2a, x * g2b = g2b * x := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left g2a_mul_g2b k).eq
  obtain ⟨hab, hcard⟩ := Sec5.isElemAbelian_sup_zpowers hA g2b_not_mem_zpowers g2b_pow_three
    hcomm
  refine ⟨hab, ?_, sup_le (Subgroup.zpowers_le.mpr g2a_mem_rootGroup)
    (Subgroup.zpowers_le.mpr g2b_mem_rootGroup)⟩
  rw [hcard, Nat.card_zpowers, orderOf_g2a]

theorem exists_E9_adjointG2_two {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    ∃ E : Subgroup (adjointGroup .G2 k), CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fintype k := Fintype.ofFinite k
  have hk' : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card, hk]
  obtain ⟨hab, hcard, hle⟩ := exists_E9_rootGroup
  obtain ⟨E₀, hE₀ab, hE₀card⟩ : ∃ E₀ : Subgroup rootGroup, CFSG.Assembly.IsElemAbelian 3 E₀ ∧
      Nat.card E₀ = 9 := by
    refine ⟨(Subgroup.zpowers g2a ⊔ Subgroup.zpowers g2b).subgroupOf rootGroup, ?_, ?_⟩
    · refine Item434Kit.isElemAbelian_of_map_injective rootGroup.subtype_injective ?_
      rw [Subgroup.map_subgroupOf_eq_of_le hle]
      exact hab
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard]
  let σ : k ≃+* ZMod 2 := (ZMod.ringEquivOfPrime k Nat.prime_two hk').symm
  let ψ : adjointGroup .G2 k ≃* rootGroup :=
    (Subgroup.equivMapOfInjective _ (glHom σ) (glHom_injective σ)).trans
      (MulEquiv.subgroupCongr (map_adjointGroup σ))
  let f : rootGroup →* adjointGroup .G2 k := (ψ.symm : rootGroup →* adjointGroup .G2 k)
  exact ⟨E₀.map f, CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 f E₀ hE₀ab,
    by rw [Subgroup.card_map_of_injective ψ.symm.injective, hE₀card]⟩

theorem exists_fixed_E9_g2 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    (α : MulAut (adjointGroup .G2 K)) (hα : α ^ 3 = 1)
    (hout : α ∉ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range) :
    ∃ E : Subgroup (adjointGroup .G2 K), CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ x ∈ E, α x = x := by
  have : CharP K 2 := CFSG.SectionRank.charP_two_of_card (f := 3) (by rw [hK]; norm_num)
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  have hK3 : ringChar K ≠ 3 := by rw [hK2]; decide
  obtain ⟨σ, hσ3, k₀, rfl⟩ := g2_order_three_field_descent hK3 (by rw [hK]; norm_num) hα hout
  have hcard := card_fixSubfield_pow σ
  rw [hσ3, hK] at hcard
  have hfix2 : Nat.card (fixSubfield σ) = 2 :=
    Nat.pow_left_injective (by norm_num : 3 ≠ 0) (hcard.trans (by norm_num))
  obtain ⟨E₁, hE₁, hE₁9⟩ := exists_E9_adjointG2_two hfix2
  set c : adjointGroup .G2 (fixSubfield σ) →* adjointGroup .G2 K :=
    ((MulAut.conj k₀ : adjointGroup .G2 K ≃* adjointGroup .G2 K) :
      adjointGroup .G2 K →* adjointGroup .G2 K).comp (g2Incl σ) with hc
  have hinj : Function.Injective c := (MulAut.conj k₀).injective.comp (g2Incl_injective σ)
  refine ⟨E₁.map c, CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hE₁,
    by rw [Subgroup.card_map_of_injective hinj, hE₁9], ?_⟩
  rintro _ ⟨y, -, rfl⟩
  have hfix : g2FieldHom K σ (g2Incl σ y) = g2Incl σ y :=
    (mem_range_g2Incl_iff hK2 σ _).mp ⟨y, rfl⟩
  change (MulAut.conj k₀ * g2FieldHom K σ * (MulAut.conj k₀)⁻¹) (MulAut.conj k₀ (g2Incl σ y)) =
    MulAut.conj k₀ (g2Incl σ y)
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hfix]

theorem chevalleyExceptionalModel_of_g28 {X : Type} [Group X] (hX : IsSmallTwoG28 X) :
    ChevalleyExceptionalModel X .G2 2 3 := by
  obtain ⟨q, hq2, hq3, hv, ⟨e⟩⟩ := hX
  have h := Census.bridgeExceptional46.g2Even q hv hq2
  rw [hq3] at h
  exact CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e h

theorem forall_not_inducesOuter_g28 {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}
    (h : Ctx434Core G A M Q) (hL : IsSmallTwoG28 (layer G ⧸ Subgroup.center (layer G)))
    (h9 : Nat.card (A.map (layerConj G)) = 9) : ∀ a ∈ A, ¬ InducesOuter a (layer G) := by
  have hS := chevalleyExceptionalModel_of_g28 hL
  have hZ : Subgroup.center (layer G) = ⊥ := center_layer_eq_bot_of_cover h
    fun E _ _ _ π hπ hC hodd => CFSG.SectionRank.g2_even_perfect_odd_cover_trivial hS π hπ hC hodd
  obtain ⟨-, K, _, _, hK, ⟨e₁⟩⟩ := hS
  have hZK := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  let eC : AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot
  exact forall_not_inducesOuter_of_fixed h hZ h9 (e₁.trans eC)
    (exists_fixed_E9_g2 (by rw [hK]; norm_num))

end Item434SmallTwoIII

section Families


theorem item434SmallTwoIII_G28_9_of (hI : Item434SmallTwoIII_G28_9Inner) : Item434SecForCard IsSmallTwoG28 9 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9
  exact hI G₀ hG₀ H G f hf hker A M Q hc hL h9
    (Item434SmallTwoIII.forall_not_inducesOuter_g28 hc hL h9)

theorem item434SmallTwoIII_G28_of (hI : Item434SmallTwoIII_G28_9Inner)
    (h27 : Item434SmallTwoIII_G28_27) : Item434SmallTwoIII_G28 :=
  item434SecFor_of_card (item434SmallTwoIII_G28_9_of hI) h27

end Families

end CFSG.RankThree.PartTwo.Sec4

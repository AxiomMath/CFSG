module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Hyper
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28RFact
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Cent
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIG28
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIOuterE9

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace Item434SmallTwoIII

section Ctx


theorem card_outer_adjointG2 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) :
    Nat.card (Outer (adjointGroup .G2 K)) = 3 := by
  obtain ⟨-, T, -, hsurj, hker, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
      (f := 3) (by norm_num) K (by rw [hK]; norm_num)
  have hker' : T.ker = CFSG.ComponentClassification.OuterAutomorphisms.inner
      (adjointGroup .G2 K) := hker
  have hle : CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup .G2 K) ≤ T.ker :=
    hker'.ge
  set Φ := QuotientGroup.lift (CFSG.ComponentClassification.OuterAutomorphisms.inner
    (adjointGroup .G2 K)) T hle
  have hΦsurj : Function.Surjective Φ := fun y => by
    obtain ⟨α, rfl⟩ := hsurj y
    exact ⟨α, QuotientGroup.lift_mk _ hle α⟩
  have hΦker : Φ.ker = ⊥ := by
    rw [QuotientGroup.ker_lift, hker', QuotientGroup.map_mk'_self]
  have : Finite (Outer (adjointGroup .G2 K)) := by
    have : Finite (MulAut (adjointGroup .G2 K)) := MulEquiv.finite_left
    infer_instance
  have hcard : Nat.card (K ≃+* K) = 3 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
      (by rw [hK]; norm_num : Nat.card K = 2 ^ 3)).1
  rw [← Subgroup.card_mul_index Φ.ker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hΦsurj,
    Subgroup.card_top, hcard, hΦker, Subgroup.card_bot, one_mul]

theorem eq_bot_of_fixed_outer {K : Type} [Field K] [Finite K] [CharP K 2]
    (M : Item434G28.G28Model K) (hK : Nat.card K = 8) {E : Subgroup ↥(adjointGroup .G2 K)}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (α : MulAut ↥(adjointGroup .G2 K)) (hα3 : α ^ 3 = 1)
    (hαout : α ∉ (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range)
    (hαE : ∀ e ∈ E, α e = e) (W : Subgroup ↥(adjointGroup .G2 K)) (hW3 : ¬ 3 ∣ Nat.card W)
    (hαW : ∀ w ∈ W, α w = w) (hEW : E ≤ Subgroup.normalizer (W : Set ↥(adjointGroup .G2 K))) :
    W = ⊥ := by
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  have hK3 : ringChar K ≠ 3 := by rw [hK2]; decide
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  obtain ⟨σ, hσ3, k, rfl⟩ := CFSG.RankThree.PartTwo.KFacts.g2_order_three_field_descent hK3 hK4
    hα3 hαout
  set φ : ↥(adjointGroup .G2 K) ≃* ↥(adjointGroup .G2 K) := (MulAut.conj k).symm with hφ
  have hfixed : ∀ w, (MulAut.conj k * CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ *
      (MulAut.conj k)⁻¹) w = w → CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ (φ w) = φ w := by
    intro w hw
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply] at hw
    have := congrArg (MulAut.conj k).symm hw
    rwa [MulEquiv.symm_apply_apply] at this
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  have hW' : W.map φ.toMonoidHom = ⊥ := by
    refine Item434G28.eq_bot_of_fixed M hK σ hσ3 (W := W.map φ.toMonoidHom)
      (E := E.map φ.toMonoidHom) ?_ ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact hfixed w (hαW w hw)
    · rintro _ ⟨e, he, rfl⟩
      exact hfixed e (hαE e he)
    · rwa [Subgroup.card_map_of_injective hinj]
    · exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hEe
    · rw [Subgroup.card_map_of_injective hinj, hE9]
    · intro e' he'
      obtain ⟨e, heE, rfl⟩ := Subgroup.mem_map.mp he'
      rw [Subgroup.mem_normalizer_iff]
      intro x
      obtain ⟨y, rfl⟩ := φ.surjective x
      have hy := Subgroup.mem_normalizer_iff.mp (hEW heE) y
      constructor
      · intro hx
        obtain ⟨y', hy'W, hy'⟩ := Subgroup.mem_map.mp hx
        have : y' = y := φ.injective hy'
        subst this
        exact Subgroup.mem_map.mpr ⟨e * y' * e⁻¹, hy.mp hy'W, by simp⟩
      · intro hx
        obtain ⟨z, hzW, hz⟩ := Subgroup.mem_map.mp hx
        have : z = e * y * e⁻¹ := φ.injective (by simpa using hz)
        exact Subgroup.mem_map.mpr ⟨y, hy.mpr (this ▸ hzW), rfl⟩
  refine (Subgroup.eq_bot_iff_forall W).mpr fun w hw => ?_
  have : φ.toMonoidHom w ∈ W.map φ.toMonoidHom := Subgroup.mem_map_of_mem _ hw
  rw [hW'] at this
  exact hinj (by simpa using Subgroup.mem_bot.mp this)

theorem false_of_g28_twentySeven {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}
    (h : Ctx434Core G A M Q) (hL : IsSmallTwoG28 (layer G ⧸ Subgroup.center (layer G)))
    (h27 : Nat.card (A.map (layerConj G)) = 27) : False := by
  have hS := chevalleyExceptionalModel_of_g28 hL
  have hZ : Subgroup.center (layer G) = ⊥ := center_layer_eq_bot_of_cover h
    fun E _ _ _ π hπ hC hodd => CFSG.SectionRank.g2_even_perfect_odd_cover_trivial hS π hπ hC hodd
  obtain ⟨-, K, _, _, hK, ⟨e₁⟩⟩ := hS
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  have : CharP K 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card hK
  obtain ⟨M'⟩ := Item434G28.exists_model (K := K) hK8
  have hZK := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  let eC : AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot
  set θ := e₁.trans eC with hθ
  have hO : Nat.card (Outer (adjointGroup .G2 K)) = 3 := card_outer_adjointG2 hK8
  have hCA : A ⊓ Subgroup.centralizer (layer G : Set G) = ⊥ := by
    have h1 := h.card_inf_mul_card_layerStar
    change _ * Nat.card (A.map (layerConj G)) = 27 at h1
    rw [h27] at h1
    rw [← Subgroup.card_eq_one]
    omega
  have hA27 := Item434Kit.card_map_quotConj h hCA θ
  have hAe := Item434Kit.isElemAbelian_map_quotConj h θ
  obtain ⟨E, hEe, hE9, hEN⟩ := exists_map_conj_le_of_card_27 hZK (by rw [hO]; norm_num) hAe hA27
  refine Item434Kit.false_of_normalizer h θ fun Y hY3 hYN => ?_
  have : Finite ↥(adjointGroup .G2 K) := Subtype.finite
  refine Item434G28.eq_bot_of_hyperplanes hZK hO hAe hA27 hEN ?_ ?_ hY3 hYN
  · intro E' hE' hE'9 x hx
    exact M'.pow_nine_of_centralizes hK8 hE' hE'9 x hx
  · intro α hα3 hαout hαE W hW3 hαW hEW
    exact eq_bot_of_fixed_outer M' hK8 hEe hE9 α hα3 hαout hαE W hW3 hαW hEW

end Ctx

end Item434SmallTwoIII

section Families


theorem item434SmallTwoIII_G28_27 : Item434SmallTwoIII_G28_27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  exact (Item434SmallTwoIII.false_of_g28_twentySeven hc hL h27).elim

end Families

end CFSG.RankThree.PartTwo.Sec4

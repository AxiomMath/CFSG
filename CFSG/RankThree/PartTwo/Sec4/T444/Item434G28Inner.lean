module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Gen
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIG28
import CFSG.RankThree.PartTwo.Sec4.Steps439

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace Item434SmallTwoIII

section Ctx

open Item434Kit Item434Alt

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem quotConj_mem_range_conj_of_inner (h : Ctx434Core G A M Q) {X : Type*} [Group X]
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {a : G} (ha : ¬ InducesOuter a (layer G)) :
    quotConj e a ∈ (MulAut.conj : X →* MulAut X).range := by
  have : (layer G).Characteristic := layer_characteristic
  obtain ⟨l, hl, hc⟩ := exists_mem_centralizer_of_not_inducesOuter ha
  have h1 : quotConj e (l⁻¹ * a) = 1 := (quotConj_eq_one_iff h.isQuasisimple e).mpr hc
  have h2 : quotConj e a = quotConj e l * quotConj e (l⁻¹ * a) := by
    rw [← map_mul, mul_inv_cancel_left]
  rw [h2, h1, mul_one, quotConj_of_mem e hl]
  exact ⟨_, rfl⟩

theorem layer_closure_eq_top (h : Ctx434Core G A M Q) {X : Type*} [Group X]
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hZ : Subgroup.center (layer G) = ⊥)
    (hgen : Subgroup.closure {x : X | ∃ ψ ∈ A.map (quotConj e), ψ ≠ 1 ∧ ψ x = x} = ⊤) :
    Subgroup.closure {y : layer G | ∃ φ ∈ A.map (layerConj G), φ ≠ 1 ∧ φ y = y} = ⊤ := by
  set ι := layerEquiv e hZ
  have hsub : {x : X | ∃ ψ ∈ A.map (quotConj e), ψ ≠ 1 ∧ ψ x = x} ⊆
      ι.toMonoidHom '' {y : layer G | ∃ φ ∈ A.map (layerConj G), φ ≠ 1 ∧ φ y = y} := by
    rintro x ⟨_, ⟨a, ha, rfl⟩, hψ1, hψx⟩
    refine ⟨ι.symm x, ⟨layerConj G a, ⟨a, ha, rfl⟩, fun h1 => hψ1 ?_, ?_⟩,
      ι.apply_symm_apply x⟩
    · exact (quotConj_eq_one_iff h.isQuasisimple e).mpr (layerConj_eq_one_iff.mp h1)
    · apply layerQuot_injective e hZ
      rw [← quotConj_layerQuot]
      have hx' : layerQuot e (ι.symm x) = x := ι.apply_symm_apply x
      rw [hx', hψx]
  have htop : (⊤ : Subgroup X) ≤ (Subgroup.closure
      {y : layer G | ∃ φ ∈ A.map (layerConj G), φ ≠ 1 ∧ φ y = y}).map ι.toMonoidHom := by
    rw [← hgen, MonoidHom.map_closure]
    exact Subgroup.closure_mono hsub
  rw [eq_top_iff]
  intro y _
  obtain ⟨z, hz, hzy⟩ := htop (Subgroup.mem_top (ι y))
  rwa [ι.injective hzy] at hz


theorem false_of_g28_inner (h : Ctx434Core G A M Q)
    (hL : IsSmallTwoG28 (layer G ⧸ Subgroup.center (layer G)))
    (h9 : Nat.card (A.map (layerConj G)) = 9) (hin : ∀ a ∈ A, ¬ InducesOuter a (layer G)) :
    False := by
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
  have hinj := conj_injective_of_center_eq_bot hZK
  have hAin : A.map (quotConj θ) ≤ (MulAut.conj : adjointGroup .G2 K →*
      MulAut (adjointGroup .G2 K)).range := by
    rintro _ ⟨a, ha, rfl⟩
    exact quotConj_mem_range_conj_of_inner h θ (hin a ha)
  set E := (A.map (quotConj θ)).comap (MulAut.conj : adjointGroup .G2 K →*
    MulAut (adjointGroup .G2 K)) with hE
  have hEmap : E.map MulAut.conj = A.map (quotConj θ) := Subgroup.map_comap_eq_self hAin
  have hA9 : Nat.card (A.map (quotConj θ)) = 9 := by
    have h27 := card_eq_card_inf_ker_mul_card_map (quotConj θ) A
    rw [h.isE27.2, ker_quotConj h.isQuasisimple θ, card_inf_centralizer_eq_three h h9] at h27
    omega
  have hE9 : Nat.card E = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hEmap, hA9]
  have hEe : CFSG.Assembly.IsElemAbelian 3 E :=
    isElemAbelian_of_map_injective hinj (hEmap ▸ isElemAbelian_map_quotConj h θ)
  have hgenE := Item434G28.G28Model.closure_fixedSet_eq_top M' hK8 hEe hE9
  have hgen : Subgroup.closure {x : adjointGroup .G2 K | ∃ ψ ∈ A.map (quotConj θ), ψ ≠ 1 ∧
      ψ x = x} = ⊤ := by
    rw [eq_top_iff, ← hgenE]
    refine Subgroup.closure_mono ?_
    rintro x ⟨ε, hε, hε1, hxε⟩
    refine ⟨MulAut.conj ε, hEmap ▸ ⟨ε, hε, rfl⟩, fun h1 => hε1 (hinj (by rw [h1]; simp)), ?_⟩
    rw [MulAut.conj_apply, ← hxε]
    group
  exact h.not_le (layer_le_of_closure_fixed h h9 (layer_closure_eq_top h θ hZ hgen))

end Ctx

end Item434SmallTwoIII

section Families


theorem item434SmallTwoIII_G28_9Inner : Item434SmallTwoIII_G28_9Inner := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9 hin
  exact (Item434SmallTwoIII.false_of_g28_inner hc hL h9 hin).elim

end Families

end CFSG.RankThree.PartTwo.Sec4

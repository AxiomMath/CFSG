module

public import CFSG.LocalAnalysis.StandardType.GGF4AutReflQuotient
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeReflPair
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder
import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Rank
import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley TableB
open CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

theorem exists_F4Three_quotient
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} (hmk : GGF4ThreeMarking Bs X) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀) (_ : CharP K₀ 2), 3 ∣ Nat.card K₀ + 1 ∧
      ∃ η : ↥X →* ↥(adjointGroup .F4 K₀), Function.Surjective η ∧
        (∀ x : ↥X, η x = 1 → (x : G) ∈ Subgroup.centralizer (X : Set G)) ∧
        (∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ 2 = 1) ∧
        Bs ≤ Subgroup.normalizer (X : Set G) ∧
        ∀ b ∈ Bs, ∃ x ∈ X, ∀ l ∈ X, b * l * b⁻¹ = x * l * x⁻¹ := by
  obtain ⟨hX, lab, hlab, hraw⟩ := hmk
  obtain ⟨_, _, _, _, _, _, _, htag, _⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨t, l, n⟩ := lab
  obtain rfl : t = .F4 := htag.1
  obtain ⟨K, _, _, hK, -, -, θ, hL, hBsN, hind⟩ := hraw
  have : CharP K 2 := charP_two_of_card hK
  set η : ↥X →* ↥(adjointGroup .F4 K) := (TableBF4.recipeEquiv K).toMonoidHom.comp (ggQuotHom θ)
  have hηs : Function.Surjective η :=
    (TableBF4.recipeEquiv K).surjective.comp (ggQuotHom_surjective θ)
  have hηk : η.ker = Subgroup.center ↥X := by
    rw [MonoidHom.ker_comp_of_injective _ _ (TableBF4.recipeEquiv K).injective, ker_ggQuotHom]
  have hZ := F4AutRefl.card_ker_dvd_two_of_adjointF4 hlab.1 hK hX η hηs hηk.le
  rw [hηk] at hZ
  have hZ2 : ∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ 2 = 1 := by
    intro z hzX hzC
    have hz : (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X := Subgroup.mem_center_iff.mpr fun w =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC w w.2)
    exact congrArg Subtype.val
      (orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard _ hz).trans hZ))
  have hker : ∀ x : ↥X, η x = 1 → (x : G) ∈ Subgroup.centralizer (X : Set G) := by
    intro x hx
    have hx' : x ∈ Subgroup.center ↥X := hηk ▸ hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx' ⟨h, hh⟩)
  refine ⟨K, inferInstance, inferInstance, inferInstance, by rw [hK]; exact hL.2.2, η, hηs, hker,
    hZ2, hBsN, F4AutRefl.exists_conj_of_inn hX θ (TableBF4.idImage_subset_inn K) hBsN hind⟩

theorem ggF4Three_rank_of_marking
    (h : GGF4ThreeSCTransvInput) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hT : GGNoTransvection 3 Bs)
    {X : Subgroup G} (hM : GGF4ThreeMarking Bs X) (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    3 ^ 4 ≤ Nat.card (ggGamma X hN).range := by
  obtain ⟨K₀, _, _, _, hq, η, hηs, hker, hZ2, -, hinner⟩ := exists_F4Three_quotient hM
  have hlow := F4AutRefl.ggRankLower_of_quotient Nat.prime_three (by decide) hcfg.2.1.2.1
    hcfg.2.1.2.2.2 hinner hZ2 η hηs hker hT (h K₀ hq)
  rw [← NbrU63.card_range_ggGamma_mul_card_inf hN] at hlow
  exact Nat.le_of_mul_le_mul_right hlow Nat.card_pos

theorem ggF4ThreeNbrRankInputStrong_of
    (h : GGF4ThreeSCTransvInput) : GGF4ThreeNbrRankInputStrong := by
  intro G _ _ B Bs x L D J hcfg hT y K hnb hM hN
  exact ggF4Three_rank_of_marking h hcfg hT hM hN

theorem card_eq_of_F4Three_marking
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) {X : Subgroup G} (hrow : GGF4ThreeMarking Bs X)
    (hR : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), 3 ^ 4 ≤ Nat.card (ggGamma X hN).range) :
    Nat.card Bs = 3 ^ 4 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
  obtain ⟨K₀, _, _, _, hq, η, -, hker, hZ2, hN, hinner⟩ := exists_F4Three_quotient hrow
  have hq2 : 3 ∣ Nat.card K₀ ^ 2 - 1 := by
    have h := Nat.sq_sub_sq (Nat.card K₀) 1
    rw [one_pow] at h
    rw [h]
    exact Dvd.dvd.mul_right hq _
  have hup := F4AutRefl.ggRankUpper_of_quotient (by decide) hcfg.2.1.2.1 hcfg.2.1.2.2.2 hinner
    hZ2 η hker fun E hE =>
      ExcFieldAutCentRankF4.card_le_pow_four Nat.prime_three (by norm_num) hq2 hE
  have hlow := hR hN
  have hmul := NbrU63.card_range_ggGamma_mul_card_inf hN
  refine le_antisymm hup ?_
  rw [← hmul]
  exact Nat.mul_le_mul_right _ hlow

theorem ggF4Three_automizer_card_lower_of_rank
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) {X : Subgroup G} (hrow : GGF4ThreeMarking Bs X)
    (hR : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), 3 ^ 4 ≤ Nat.card (ggGamma X hN).range) :
    2 ^ 4 * Nat.factorial 4 ≤ Nat.card (ggAutomizer X Bs) := by
  obtain ⟨K₀, _, _, _, _, η, hηs, hker, hZ2, _, hinner⟩ := exists_F4Three_quotient hrow
  exact (F4AutRefl.ggF4AutRefl_of_quotient (by decide : Odd 3) hcfg.2.1.2.1 hcfg.2.1.2.2.2
    hinner hZ2 (card_eq_of_F4Three_marking hcfg hrow hR) η hηs hker
    (fun E hE hcard => ggAutomizer_adjointF4_of_card Nat.prime_three (by decide) hE hcard)).1

theorem ggF4Three_framePair_of_rank
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) {X : Subgroup G} (hrow : GGF4ThreeMarking Bs X)
    (hR : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), 3 ^ 4 ≤ Nat.card (ggGamma X hN).range) :
    ∃ c₁ ∈ ggAutomizer X Bs, ∃ c₂ ∈ ggAutomizer X Bs, GGIsReflection 3 c₁ ∧
      GGIsReflection 3 c₂ ∧ 4 ∣ orderOf (c₁ * c₂) := by
  obtain ⟨K₀, _, _, _, -, η, hηs, hker, hZ2, -, hinner⟩ := exists_F4Three_quotient hrow
  exact F4AutRefl.ggFramePair_of_quotient (by decide) hcfg.2.1.2.1 hcfg.2.1.2.2.2 hinner hZ2
    (card_eq_of_F4Three_marking hcfg hrow hR) η hηs hker
    (fun E hE hcard => F4AutWeyl.exists_reflPair_of_card Nat.prime_three (by norm_num) hE hcard)

theorem ggRow_absurd_of_framePair {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G}
    (hle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hpair : ∃ c₁ ∈ ggAutomizer K Bs, ∃ c₂ ∈ ggAutomizer K Bs, GGIsReflection p c₁ ∧
      GGIsReflection p c₂ ∧ 4 ∣ orderOf (c₁ * c₂)) : False := by
  obtain ⟨c₁, hc₁, c₂, hc₂, hr₁, hr₂, h4⟩ := hpair
  have hC₁ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 (hle hc₁) hr₁
  have hC₂ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 (hle hc₂) hr₂
  rcases ggCoxRefl_mul_orderOf_le_three hpres.1 hle3 hC₁ hC₂ with h | h
  · have h42 : 4 ∣ 2 := h4.trans (orderOf_dvd_of_pow_eq_one h)
    omega
  · have h43 : 4 ∣ 3 := h4.trans (orderOf_dvd_of_pow_eq_one h)
    omega

theorem ggF4ThreeNbrRankInput_of_KG1
    (h : GGF4ThreeSCTransvInput) : GGF4ThreeNbrRankInput :=
  ggF4ThreeNbrRankInput_of_strong (ggF4ThreeNbrRankInputStrong_of h)

theorem ggRow_absurd_F4Three_of_KG1
    (h : GGF4ThreeSCTransvInput) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {X : Subgroup G}
    (hle : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦) (hrow : GGF4ThreeMarking Bs X) : False :=
  ggRow_absurd_of_framePair hcfg hpres hle3 hle
    (ggF4Three_framePair_of_rank hcfg.1.1 hrow fun hN =>
      ggF4Three_rank_of_marking h hcfg.1.1 hcfg.1.2.2.2.1 hrow hN)

end CFSG.StandardType

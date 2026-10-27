module

public import CFSG.LocalAnalysis.StandardType.GGNbrTwE6Prop87
public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
import CFSG.HardMathSupport.Timmesfeld.Coordinator.ElemAbelianComplement
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Holds
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc3
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcReduction
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint

theorem ggNbr_rank_dichotomy_twE6 {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (hlr : GGTwE6LocalRank R)
    (hcyc : ∀ E : Subgroup K, E ≤ Subgroup.center K → IsElemAbelian 3 E → Nat.card E ≤ 3)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    3 ^ 5 ≤ Nat.card (ggGamma K hN).range ∨
      (B = Bs ∧ Nat.card Bs = 3 ^ 5 ∧ LargeEvenTwoLocalRank 3 G = 5 ∧
        Nat.card (ggGamma K hN).range = 3 ^ 4 ∧
        Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y) := by
  classical
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSHat 3 B y K := hnb.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hN
  obtain ⟨U, hU, hU2, E, hEU, hEab, hEcase⟩ := hlr ↥K hK θ
  set E₀ : Subgroup ↥K := E ⊓ Subgroup.center ↥K with hE₀def
  have hE₀E : E₀ ≤ E := by rw [hE₀def]; exact inf_le_left
  have hE₀le3 : Nat.card E₀ ≤ 3 :=
    hcyc E₀ (by rw [hE₀def]; exact inf_le_right)
      (CFSG.Open.IsElemAbelian.mono hEab hE₀E)
  have hineq : 3 ^ 4 * Nat.card E₀ ≤ Nat.card E := by
    rcases hEcase with hE5 | ⟨hE4, hEbot⟩
    · rw [hE5]
      calc 3 ^ 4 * Nat.card E₀ ≤ 3 ^ 4 * 3 := Nat.mul_le_mul_left _ hE₀le3
        _ = 3 ^ 5 := by norm_num
    · have hE₀card : Nat.card E₀ = 1 := by
        rw [hEbot]
        simp
      rw [hE4, hE₀card]
      norm_num
  obtain ⟨E', hE'E, hE'ab, hE'card, hE'Z₀⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.exists_elemAbelian_le_inf_eq_bot
      hp hEab hE₀E 4 hineq
  have hE'Z : E' ⊓ Subgroup.center ↥K = ⊥ := by
    rw [hE₀def] at hE'Z₀
    rw [← inf_assoc, inf_eq_left.mpr hE'E] at hE'Z₀
    exact hE'Z₀
  have hE'U : E' ≤ Subgroup.normalizer (U : Set ↥K) := hE'E.trans hEU
  set C : Subgroup G := Bs ⊓ Subgroup.centralizer (K : Set G) with hC
  have hCel : IsElemAbelian 3 C := CFSG.Open.IsElemAbelian.mono hBs inf_le_left
  have hCf : ∀ g ∈ C, ∀ j : ↥K, K.subtype j * g = g * K.subtype j := by
    intro g hg j
    exact Subgroup.mem_centralizer_iff.mp hg.2 j j.2
  have hbound := card_mul_pow_le_of_normalizes hp K.subtype K.subtype_injective hCel hCf
    hU hU2 hE'U hE'ab hE'Z (k := 4) hE'card
  rw [← hS.1.2.1] at hbound
  have hyB : y ∈ B := hS.2.1
  have hyC : y ∈ C := by
    have h1 : y ∈ B ⊓ Subgroup.centralizer (K : Set G) := by
      rw [inf_centralizer_eq_zpowers_of_sHat hS]
      exact Subgroup.mem_zpowers y
    exact ⟨hBBs h1.1, h1.2⟩
  have hzycard : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hS.1.1.2 y hyB) hS.2.2.1]
  have hzC : Subgroup.zpowers y ≤ C := Subgroup.zpowers_le.mpr hyC
  have h3C : 3 ≤ Nat.card C := by
    rw [← hzycard]
    exact Subgroup.card_le_of_le hzC
  have h5m : 5 ≤ LargeEvenTwoLocalRank 3 G := by
    have h1 : 3 ^ 5 ≤ Nat.card B := by
      calc 3 ^ 5 = 3 * 3 ^ 4 := by norm_num
        _ ≤ Nat.card C * 3 ^ 4 := Nat.mul_le_mul_right _ h3C
        _ ≤ Nat.card B := hbound
    rw [hS.1.2.1] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
  have hcB : Nat.card (ggGamma K hBN).range * 3 = Nat.card B :=
    card_range_ggGamma_mul_of_sHat hp hS hBN
  have hle : (ggGamma K hBN).range ≤ (ggGamma K hN).range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  by_cases hm6 : 6 ≤ LargeEvenTwoLocalRank 3 G
  ·
    left
    have hm1 : 1 ≤ LargeEvenTwoLocalRank 3 G := by omega
    have hgm : Nat.card (ggGamma K hBN).range * 3 = 3 ^ LargeEvenTwoLocalRank 3 G := by
      rw [hcB, hS.1.2.1]
    have hgm' : Nat.card (ggGamma K hBN).range =
        3 ^ (LargeEvenTwoLocalRank 3 G - 1) := by
      have h3m : 3 ^ LargeEvenTwoLocalRank 3 G =
          3 ^ (LargeEvenTwoLocalRank 3 G - 1) * 3 := by
        nth_rewrite 1 [← Nat.sub_add_cancel hm1]
        rw [pow_succ]
      apply Nat.mul_right_cancel (by norm_num : 0 < 3)
      rw [hgm]
      exact h3m
    exact (Nat.pow_le_pow_right (by norm_num) (by omega : 5 ≤ _ - 1)).trans
      (hgm' ▸ Subgroup.card_le_of_le hle)
  ·
    have hm5 : LargeEvenTwoLocalRank 3 G = 5 := by omega
    have hgm4 : Nat.card (ggGamma K hBN).range = 3 ^ 4 := by
      have h1 : Nat.card (ggGamma K hBN).range * 3 = 3 ^ 5 := by
        rw [hcB, hS.1.2.1, hm5]
      apply Nat.mul_right_cancel (by norm_num : 0 < 3)
      rw [h1]; norm_num
    have h4le : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range := by
      rw [← hgm4]
      exact Subgroup.card_le_of_le hle
    have hC3 : Nat.card C ≤ 3 := by
      have h1 : Nat.card C * 3 ^ 4 ≤ 3 ^ 5 := by
        rw [hS.1.2.1, hm5] at hbound
        exact hbound
      norm_num at h1 ⊢
      omega
    have hCZy : C = Subgroup.zpowers y :=
      (Subgroup.eq_of_le_of_card_ge hzC (by rw [hzycard]; exact hC3)).symm
    have hmul := card_ggAutsOf_mul_card hN
    change Nat.card (ggGamma K hN).range * Nat.card C = Nat.card Bs at hmul
    have hCcard : Nat.card C = 3 := by rw [hCZy, hzycard]
    have hrange_elab : IsElemAbelian 3 (ggGamma K hN).range :=
      isElemAbelian_ggAutsOf hN hBs
    obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp (CFSG.Open.IsElemAbelian.isPGroup hrange_elab)
    have h4c : 4 ≤ c := by
      have h1 : 3 ^ 4 ≤ 3 ^ c := by rw [← hc]; exact h4le
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
    by_cases h5c : 5 ≤ c
    · left
      exact (Nat.pow_le_pow_right (by norm_num) h5c).trans (le_of_eq hc.symm)
    · right
      have hc4 : c = 4 := by omega
      have hBs5 : Nat.card Bs = 3 ^ 5 := by
        rw [← hmul, hCcard, hc, hc4]; norm_num
      have hBeq : Nat.card B = Nat.card Bs := by
        calc Nat.card B = Nat.card (ggGamma K hBN).range * 3 := hcB.symm
          _ = 3 ^ 4 * 3 := by rw [hgm4]
          _ = 3 ^ 5 := by norm_num
          _ = Nat.card Bs := hBs5.symm
      refine ⟨Subgroup.eq_of_le_of_card_ge hBBs hBeq.ge, hBs5, hm5, ?_, ?_⟩
      · rw [hc, hc4]
      · simpa [hC] using hCZy

end CFSG.StandardType

end

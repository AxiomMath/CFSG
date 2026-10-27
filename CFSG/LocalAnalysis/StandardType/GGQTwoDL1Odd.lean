module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1OddLeaves
public import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)}

theorem qtwoDL1_odd_centralizer_of_ne (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hne : B ≠ Bs) : Odd (Nat.card ↥(Subgroup.centralizer (Bs : Set G))) := by
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hcfg
  have hBs : GGBstar p B Bs := hcfg.1.1.2.1
  have hS : LargeEvenSStar p B x L := hcfg.1.1.1.2.2.2.2.2.2.1
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(Subgroup.centralizer (Bs : Set G)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  set T : Subgroup G := Subgroup.zpowers (t : G) with hTdef
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one])
  have hT1 : T ≠ ⊥ := by
    intro h
    have h1 : (t : G) = 1 := Subgroup.zpowers_eq_bot.mp h
    rw [h1, orderOf_one] at ht'
    exact absurd ht' (by norm_num)
  have hBsC : Bs ≤ Subgroup.centralizer (T : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hbt : Commute b (t : G) := Subgroup.mem_centralizer_iff.mp t.2 b hb
    exact (hbt.zpow_right n).eq.symm
  have hBsT : Bs ≤ Subgroup.normalizer (T : Set G) :=
    hBsC.trans (Subgroup.centralizer_le_normalizer (T : Set G))
  have hc := TableB.card_le_of_twoLocal hp ⟨T, hT1, hT2, rfl⟩ hBsT hBs.2.1
  rw [← hS.1.2.1] at hc
  exact hne (Subgroup.eq_of_le_of_card_ge hBs.1 hc)

@[expose] def QTwoDL1InvFix (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  ∀ X : Subgroup G, (X = L ∨ ∃ y : G, GGNbr p B x D J y X) →
    ∀ t ∈ Subgroup.centralizer (Bs : Set G), t ∈ Subgroup.normalizer (X : Set G) → t ^ 2 = 1 →
      t ∈ Subgroup.centralizer (X : Set G)

theorem qtwoDL1_odd_centralizer_of_invFix (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hpJ : p ∣ Nat.card J)
    (hfix : QTwoDL1InvFix p B Bs x L D J) :
    Odd (Nat.card ↥(Subgroup.centralizer (Bs : Set G))) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(Subgroup.centralizer (Bs : Set G)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have ht2 : (t : G) ^ 2 = 1 := by rw [← ht']; exact pow_orderOf_eq_one _
  set T : Subgroup G := Subgroup.zpowers (t : G) with hTdef
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one])
  have hT1 : T ≠ ⊥ := by
    intro h
    have h1 : (t : G) = 1 := Subgroup.zpowers_eq_bot.mp h
    rw [h1, orderOf_one] at ht'
    exact absurd ht' (by norm_num)
  have htD : (t : G) ∈ Subgroup.centralizer (D : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (SecFiveL1Odd.le_bstar hcfg)) t.2
  have htNL : (t : G) ∈ Subgroup.normalizer (L : Set G) :=
    SecFiveL1Odd.centralizer_le_normalizer_L ha₀ hcfg htD
  have htL : (t : G) ∈ Subgroup.centralizer (L : Set G) :=
    hfix L (Or.inl rfl) (t : G) t.2 htNL ht2
  have hTL : T ≤ Subgroup.centralizer (L : Set G) := Subgroup.zpowers_le.mpr htL
  have hJL : J ≤ L := SecFiveL1Odd.J_le hL hcfg hpJ (Or.inl rfl)
  have hTJ : T ≤ Subgroup.centralizer (J : Set G) :=
    hTL.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hJL))
  have hTD : T ≤ Subgroup.centralizer (D : Set G) := Subgroup.zpowers_le.mpr htD
  have hTK : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      T ≤ Subgroup.centralizer (K : Set G) := by
    intro y K hK
    have htNK : (t : G) ∈ Subgroup.normalizer (K : Set G) :=
      SecFiveL1Odd.centralizer_le_normalizer_nbr ha₀ hL hcfg hpJ hK htD
    exact Subgroup.zpowers_le.mpr (hfix K (Or.inr ⟨y, hK⟩) (t : G) t.2 htNK ht2)
  have hG0T : ggG0 p B x L D J ≤ Subgroup.centralizer (T : Set G) := by
    refine sup_le (Subgroup.le_centralizer_iff.mp hTL) ?_
    refine iSup_le fun y => iSup_le fun K => iSup_le fun hK => ?_
    exact Subgroup.le_centralizer_iff.mp (hTK y K hK)
  have hT0 : T ≤ Subgroup.centralizer (ggG0 p B x L D J : Set G) :=
    Subgroup.le_centralizer_iff.mpr hG0T
  exact SecFiveL1Odd.false_of_le_centralizer_ggG0 ha₀ hL hcfg hpJ hT2 hT1
    (le_inf hTD hTJ) hT0

end CFSG.StandardType.QTwo

end

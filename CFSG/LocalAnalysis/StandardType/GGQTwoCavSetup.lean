module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCavImage
public import CFSG.LocalAnalysis.StandardType.GGQTwoCentralizerLift
public import CFSG.LocalAnalysis.StandardType.GGQTwoOriginalNormalizerLift
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer

public noncomputable section

namespace CFSG.StandardType.QTwoCav

open CFSG.Assembly TableB

variable {G : Type} [Group G] [Finite G] {p : ℕ}
  {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem d_le_normalizer (hS : GGQTwoSetting p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    D ≤ Subgroup.normalizer (L : Set G) :=
  hS.1.1.2.2.1.1.trans (hS.1.1.2.1.1.trans hN)

theorem gamma_d_card (hp : p.Prime) (hS : GGQTwoSetting p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (ggGamma L (d_le_normalizer hS hN)).range = p := by
  have hSS : LargeEvenSStar p B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hpre : LargeEvenStdSubPre p B x L D J := hS.1.1.2.2.1
  obtain ⟨hDB, hD, hcardD, hxD, -, -, -⟩ := hpre
  have hC : D ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian hp hD hxD hSS.2.2.1
      hSS.2.2.2.1.1 hSS.2.2.2.2
  have hker : (ggGamma L (d_le_normalizer hS hN)).ker =
      (Subgroup.zpowers x).subgroupOf D := by
    rw [gamma_ker]
    ext d
    change (d : G) ∈ Subgroup.centralizer (L : Set G) ↔ (d : G) ∈ Subgroup.zpowers x
    exact ⟨fun h => hC ▸ (show (d : G) ∈ D ⊓ Subgroup.centralizer (L : Set G) from
      ⟨d.property, h⟩), fun h => (show (d : G) ∈ D ⊓ Subgroup.centralizer (L : Set G) from
      hC.symm ▸ h).2⟩
  have hkerCard : Nat.card (ggGamma L (d_le_normalizer hS hN)).ker = p := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hxD)).toEquiv, Nat.card_zpowers]
    let : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime (hD.2 x hxD) hSS.2.2.1
  have horder := Subgroup.card_ker_mul_card_range (ggGamma L (d_le_normalizer hS hN))
  rw [hkerCard, hcardD, pow_two] at horder
  exact Nat.mul_left_cancel hp.pos horder

theorem pow_three_le_beta_card (hS : GGQTwoSetting p B Bs x L D J)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    p ^ 3 ≤ Nat.card (ggBeta L θ hN).range := by
  letI : Finite R := Finite.of_surjective θ θ.surjective
  have hB : B ≤ Bs := hS.1.1.2.1.1
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hB.trans hN
  have h := card_range_ggBeta_bstar hS.1.1 hS.2.1.1 θ hBN hN
  exact h.2.1.trans (Subgroup.card_le_of_le (range_ggBeta_le θ hB hBN hN))

theorem three_le_exponent_of_beta_index (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p.Prime) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {r : ℕ}
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ r) :
    3 ≤ r := by
  have h := pow_three_le_beta_card hS θ hN
  rw [beta_card hS.2.1.1 θ hN, hidx] at h
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h

end CFSG.StandardType.QTwoCav

end

module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCavHeartImage
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavAutomizer
public import CFSG.LocalAnalysis.StandardType.GGQTwoUnitaryHeartAutomizer

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGQ2CavOfTBHeartInner : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQ2TBHeart p Bs L →
      Bs ≤ L ⊔ Subgroup.zpowers x → ¬ CFSG.AGLEmbedding.IsAltTwoP 3 J →
        ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
          4 ∣ Nat.card (ggAutomizer
            ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L))
            (ggGamma L hN).range)

theorem ggQ2_cav_of_tbHeart (h : GGQ2CavOfTBHeartInner) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3) (hTB : GGQ2TBHeart p Bs L)
    (M : GGQ2LDatum p Bs L x) (hM : M.HeartShape) : 4 ∣ Nat.card (ggAutomizer J Bs) := by
  obtain ⟨_, lab, _, hraw⟩ := hS.2.1
  obtain ⟨_, _, _, _, _, _, _, _, hN, _⟩ := largeEvenRawDatum_exists hraw
  by_cases hJ : CFSG.AGLEmbedding.IsAltTwoP 3 J
  · rw [QTwoB2Cav.card_automizer_original_of_setting hS hp3 hN hJ]
  · have hcard := QTwoCav.card_automizer_inner_image_eq_of_setting hS
      (by rw [hp3]; exact Nat.prime_three) (by omega) hN
    rw [← hcard]
    exact h hS hp3 hTB
      (M.bstar_le_sup_zpowers_of_heartShape (by rw [hp3]; norm_num) hN hM) hJ hN

theorem ggQ2_cavOfTBHeart_of_inner (h : GGQ2CavOfTBHeartInner) : GGQ2CavOfTBHeart := by
  intro G _ _ p B Bs x L D J hS hp3 _ _ hTB M hM
  exact ggQ2_cav_of_tbHeart h hS hp3 hTB M hM


namespace QTwoUnitaryCav

theorem four_dvd_original_automizer_of_heart_label
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J : Subgroup G} {x : G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo p lab) (htag : lab.tag = .twA)
    (h3d : 3 ∣ lab.rank + 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ (lab.rank - 1))
    (hsup : Bs ≤ L ⊔ Subgroup.zpowers x) :
    4 ∣ Nat.card (ggAutomizer J Bs) := by
  have hp : p.Prime := by rw [hp3]; exact Nat.prime_three
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨_, lab₀, _, hraw⟩ := hS.2.1
  obtain ⟨_, _, _, _, _, _, _, _, hN₀, _⟩ := largeEvenRawDatum_exists hraw
  have hr : 3 ≤ lab.rank - 1 := QTwoCav.three_le_exponent_of_beta_index hS hp
    (MulEquiv.refl (L ⧸ Subgroup.center L)) hN₀ hidx
  have hd6 : 6 ≤ lab.rank + 1 := by
    obtain ⟨k, hk⟩ := h3d
    omega
  have hdq : (lab.rank + 1, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have := congrArg Prod.fst h
    omega
  have hSS : LargeEvenSStar p B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_of_le_centralizer hSS.2.2.2.1.1
  obtain ⟨K, hField, hFin, h, hK, θ, hN, Q, hQ, I, hI4, hblock, hfr, hinner, _, hCard, _⟩ :=
    exists_quotient_J_block_of_le_sup_zpowers hS hp3 hq2 htag h3d hd6 hdq hmark hidx hsup hxC
  letI : Field K := hField
  letI : Finite K := hFin
  have hfour := four_dvd_ggAutomizer_frameBlock (h := h) (Q := Q) (hQ := hQ)
    hK hd6 h3d hfr hinner hCard I hI4
  rw [← hblock] at hfour
  rw [QTwoCav.card_automizer_quotient_image_eq θ hS.2.1.1 hN,
    QTwoCav.card_automizer_inner_image_eq_of_setting hS hp (by omega) hN] at hfour
  exact hfour

end QTwoUnitaryCav

theorem ggQ2_cavOfTBHeartInner_holds : GGQ2CavOfTBHeartInner := by
  intro G _ _ p B Bs x L D J hS hp3 hTB hsup _ hN
  rw [QTwoCav.card_automizer_inner_image_eq_of_setting hS
    (by rw [hp3]; exact Nat.prime_three) (by omega) hN]
  obtain ⟨lab, hlab, hM, htag, hidx⟩ := hTB
  have hmark := QTwoCav.innerDiagOnLabel_of_setting hS hM
  rcases htag with ⟨htwA, h3d⟩ | htwE6
  · exact QTwoUnitaryCav.four_dvd_original_automizer_of_heart_label hS hp3 hlab htwA h3d
      hmark (by simpa only [GGQ2LieRank, htwA] using hidx) hsup
  · exact QTwoE6.four_dvd_original_automizer_of_heart_label hS hp3 hlab htwE6
      hmark (by simpa only [GGQ2LieRank, htwE6] using hidx) hsup

theorem ggQ2_cavOfTBHeart_holds : GGQ2CavOfTBHeart :=
  ggQ2_cavOfTBHeart_of_inner ggQ2_cavOfTBHeartInner_holds

end CFSG.StandardType

end

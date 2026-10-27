module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACSymp
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2E7Rank
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2ExceptionalAction
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaExcPlusAux2
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48RkF4Holds
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkConfig
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkTwE6
public import CFSG.LocalAnalysis.StandardType.GGF4OrderThreeRank
public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Rank
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavHeartReduction
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavAutomizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration

theorem ggQ2Exc_label_n_eq_one {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hq : GGLabQTwo 3 lab) : lab.n = 1 := by
  have h1 : 1 ≤ lab.n := hlab.1
  have h2 : lab.n < 2 := hq
  omega

theorem ggQ2F4_lower
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hmarkN1 : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab'.tag = .F4 ∧ lab'.n = 1))
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)} :
    3 ^ 4 ≤ Nat.card (ggGamma L hN).range := by
  subst hp
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, hBsE, hxBs, hLx, h4⟩ := hcfg.tableB_facts
  have hSst : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have h5 : 3 ^ 5 ≤ Nat.card Bs :=
    ggL48F4TwoThree_pow_five_le_card ggL48F4TwoThreeConfigInput_holds hcfg.1 hcfg.2.1 h4 hmarkN1
  have hmul := card_range_ggGamma_mul_of (p := 3) Nat.prime_three hBsE hxBs hSst.2.2.1 hLx
    hSst.2.2.2.2 hN
  have h7 : (3 : ℕ) ^ 5 = 3 ^ 4 * 3 := by norm_num
  rw [h7, ← hmul] at h5
  exact Nat.le_of_mul_le_mul_right h5 (by norm_num)

theorem card_le_pow_four_mulAut
    {K : Type} [Field K] [Finite K] [instCharP : CharP K 2]
    (hK : Nat.card K = 2) {E : Subgroup (MulAut (TableBF4.RecipeGroup K))}
    (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 4 :=
  TableBF4Two.card_le_mulAut hK hE

theorem ggQ2F4_upper
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hL : GGInnerDiagOnLabel (fun _ lab => GGLabQTwo p lab ∧ lab.tag = .F4) p Bs L)
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hr : 3 ^ 4 ≤ Nat.card (ggGamma L hN).range) :
    Nat.card (ggGamma L hN).range = 3 ^ 4 := by
  subst hp
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, _, I, F, -, -, θ₀, ⟨⟨hq, htag⟩, -, -⟩⟩ := largeEvenRawDatum_exists hraw
  have hn1 : lab.n = 1 := ggQ2Exc_label_n_eq_one hlab hq
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, hBsE, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hSst : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  obtain ⟨t, r, n⟩ := lab
  have ht : t = .F4 := htag
  subst ht
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, instF, instFin, hK, hQ⟩ := hraw
  obtain ⟨-, -, θ, -⟩ := hQ
  have hK2 : Nat.card K = 2 := by
    rw [hK, hn1]
    norm_num
  have hchar : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK2, pow_one])
  have hmul := card_range_ggGamma_mul_of (p := 3) Nat.prime_three hBsE hxBs hSst.2.2.1 hLx
    hSst.2.2.2.2 hN
  have hcβ := card_range_ggBeta_mul_of (p := 3) Nat.prime_three hBsE hxBs hSst.2.2.1 hLx
    hSst.2.2.2.2 hperf θ hN
  have hAβ : Nat.card (ggGamma L hN).range = Nat.card (ggBeta L θ hN).range :=
    Nat.eq_of_mul_eq_mul_right Nat.prime_three.pos (hmul.trans hcβ.symm)
  have hup : Nat.card (ggBeta L θ hN).range ≤ 3 ^ 4 :=
    card_le_pow_four_mulAut (instCharP := hchar) hK2
      (isElemAbelian_range_ggBeta θ hBsE hN)
  rw [hAβ]
  exact le_antisymm hup (hAβ ▸ hr)

theorem ggQ2TBFull_of_F4
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hL : GGInnerDiagOnLabel (fun _ lab => GGLabQTwo p lab ∧ lab.tag = .F4) p Bs L) :
    GGQ2TBFull p Bs L := by
  subst hp
  have hLkeep := hL
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, _, I, F, -, -, -, ⟨⟨hq, htag⟩, hBsN, -⟩⟩ := largeEvenRawDatum_exists hraw
  have hn1 : lab.n = 1 := ggQ2Exc_label_n_eq_one hlab hq
  have hmarkN1 : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab'.tag = .F4 ∧ lab'.n = 1) :=
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, hθ⟩ => ⟨hs, hna, θ, htag, hn1⟩) hraw⟩
  have hmarkLab : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab) :=
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, hθ⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  have hr := ggQ2F4_lower hS rfl hmarkN1 (hN := hBsN)
  have hA4 := ggQ2F4_upper hS rfl hLkeep (hN := hBsN) hr
  have hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ 4 := by
    rw [← QTwoCav.gamma_card hBsN, hA4]
  obtain ⟨t, r, n⟩ := lab
  have ht : t = .F4 := htag
  subst ht
  refine ⟨⟨.F4, r, n⟩, hq, hmarkLab, ?_⟩
  simpa [GGQ2LieRank, htag] using hidx

theorem ggQ2E7_index
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hmark : LargeEvenMarking L (fun lab R _ I _ θ =>
      (((GGLabQTwo p lab ∧ lab.tag = .E7) ∧
        Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)) ∧
      GGExcPlusWeylModelSCr .E7 3 6 R I)) :
    ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ 7 := by
  subst hp
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨R, _, I, F, hsimple, hna, θ, hP⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨⟨⟨hq, htag⟩, hBsN, hind⟩, hmodel⟩ := hP
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨hpr, hBsE, hxBs, hLx, h4⟩ := hcfg.tableB_facts
  have hSst : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSst.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hBcard : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G :=
    hcfg.1.2.2.2.2.2.2.1.1.2.1
  have hmarkTag : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab'.tag = .E7) :=
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ', hθ⟩ => ⟨hs, hna, θ', htag⟩) hraw⟩
  have hm7 : 7 ≤ LargeEvenTwoLocalRank 3 G := seven_le_twoLocalRank_of_e7Tag hcfg hmarkTag
  have hBsge : 3 ^ 7 ≤ Nat.card Bs :=
    (Nat.pow_le_pow_right (by norm_num) hm7).trans (hBcard ▸ Subgroup.card_le_of_le hcfg.2.1.1)
  have hmul := card_range_ggGamma_mul_of (p := 3) Nat.prime_three hBsE hxBs hx1 hLx
    hSst.2.2.2.2 hBsN
  have hr : 3 ^ 6 ≤ Nat.card (ggGamma L hBsN).range := by
    have h7 : (3 : ℕ) ^ 7 = 3 ^ 6 * 3 := by norm_num
    rw [h7, ← hmul] at hBsge
    exact Nat.le_of_mul_le_mul_right hBsge (by norm_num)
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range := le_trans (by norm_num) hr
  have hTB : GGTorusTBGroup 3 6 R I L (ggQuotHom θ) (ggGamma L hBsN).range :=
    ggTorusTBGroup_of_marking Nat.prime_three hBsE hSC hperf θ hBsN
      (fun b hb => ggLAut_mem_of_induces L θ hBsN hind hb) hr h3
  obtain ⟨Φ, -⟩ := hmodel L (ggQuotHom θ) (ggGamma L hBsN).range hTB
  have hA7 : Nat.card (ggGamma L hBsN).range = 3 ^ 7 := by
    rw [Nat.card_congr Φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_zmod, Nat.card_fin]
    have hrank : CFSG.Blueprint.Chevalley.Tag.E7.rank = 7 := rfl
    rw [hrank]
  rw [← QTwoCav.gamma_card hBsN, hA7]

theorem ggQ2TBFull_of_E7
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hL : GGInnerDiagOnLabel (fun _ lab => GGLabQTwo p lab ∧ lab.tag = .E7) p Bs L) :
    GGQ2TBFull p Bs L := by
  subst hp
  have hall : ∀ lab, LargeEvenInLambda2 lab → (GGLabQTwo 3 lab ∧ lab.tag = .E7) →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard
        fun R _ I _ => GGExcPlusWeylModelSCr .E7 3 6 R I) := by
    intro lab hlab hs
    have hn1 : lab.n = 1 := ggQ2Exc_label_n_eq_one hlab hs.1
    have hpn : 3 ∣ 2 ^ lab.n + 1 := by rw [hn1]; norm_num
    have h0 := ggNEE_largeEvenLabelAll_model_excPlus (p := 3) Nat.prime_three (by norm_num)
      (lab := lab) (Or.inl hs.2) hpn
    rw [show ggNEE_tagOf lab.tag = .E7 by simp [ggNEE_tagOf, hs.2],
      show ggNbrExcPlusRank lab.tag = 6 by simp [ggNbrExcPlusRank, hs.2]] at h0
    exact LargeEvenLabelAll.mono (fun R _ I F h _ _ => h) h0
  have hmark := largeEvenMarking_and_labelAll_simple (S := fun lab => GGLabQTwo 3 lab ∧
      lab.tag = .E7) (P' := fun R _ I _ => GGExcPlusWeylModelSCr .E7 3 6 R I)
    hall (fun _ _ _ _ _ _ h => h.1) hL
  have hidx := ggQ2E7_index hS rfl hmark
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨R, _, I, F, -, -, -, ⟨⟨⟨hq, htag⟩, -, -⟩, -⟩⟩ :=
    largeEvenRawDatum_exists hraw
  refine ⟨lab, hq, ?_, ?_⟩
  · exact ⟨hperf, lab, hlab, largeEvenRawDatum_mono (fun R _ I F h => by
      obtain ⟨hs, hna, θ, hP⟩ := h
      exact ⟨hs, hna, θ, rfl⟩) hraw⟩
  · simpa [GGQ2LieRank, htag] using hidx

theorem ggQ2E8_index
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hmark : LargeEvenMarking L (fun lab R _ I _ θ =>
      (((GGLabQTwo p lab ∧ lab.tag = .E8) ∧
        Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)) ∧
      GGExcPlusWeylModelSCr .E8 3 7 R I)) :
    ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ 8 := by
  subst hp
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨R, _, I, F, hsimple, hna, θ, hP⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨⟨⟨hq, htag⟩, hBsN, hind⟩, hmodel⟩ := hP
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨hpr, hBsE, hxBs, hLx, h4⟩ := hcfg.tableB_facts
  have hSst : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSst.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hBcard : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G :=
    hcfg.1.2.2.2.2.2.2.1.1.2.1
  have hmarkTag : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab'.tag = .E8) :=
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ', hθ⟩ => ⟨hs, hna, θ', htag⟩) hraw⟩
  have hm8 : 8 ≤ LargeEvenTwoLocalRank 3 G :=
    Q2Exceptional.eight_le_twoLocalRank_of_e8 hcfg hmarkTag
  have hBsge : 3 ^ 8 ≤ Nat.card Bs :=
    (Nat.pow_le_pow_right (by norm_num) hm8).trans (hBcard ▸ Subgroup.card_le_of_le hcfg.2.1.1)
  have hmul := card_range_ggGamma_mul_of (p := 3) Nat.prime_three hBsE hxBs hx1 hLx
    hSst.2.2.2.2 hBsN
  have hr : 3 ^ 7 ≤ Nat.card (ggGamma L hBsN).range := by
    have h8 : (3 : ℕ) ^ 8 = 3 ^ 7 * 3 := by norm_num
    rw [h8, ← hmul] at hBsge
    exact Nat.le_of_mul_le_mul_right hBsge (by norm_num)
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range := le_trans (by norm_num) hr
  have hTB : GGTorusTBGroup 3 7 R I L (ggQuotHom θ) (ggGamma L hBsN).range :=
    ggTorusTBGroup_of_marking Nat.prime_three hBsE hSC hperf θ hBsN
      (fun b hb => ggLAut_mem_of_induces L θ hBsN hind hb) hr h3
  obtain ⟨Φ, -⟩ := hmodel L (ggQuotHom θ) (ggGamma L hBsN).range hTB
  have hA8 : Nat.card (ggGamma L hBsN).range = 3 ^ 8 := by
    rw [Nat.card_congr Φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_zmod, Nat.card_fin]
    have hrank : CFSG.Blueprint.Chevalley.Tag.E8.rank = 8 := rfl
    rw [hrank]
  rw [← QTwoCav.gamma_card hBsN, hA8]

theorem ggQ2TBFull_of_E8
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hL : GGInnerDiagOnLabel (fun _ lab => GGLabQTwo p lab ∧ lab.tag = .E8) p Bs L) :
    GGQ2TBFull p Bs L := by
  subst hp
  have hall : ∀ lab, LargeEvenInLambda2 lab → (GGLabQTwo 3 lab ∧ lab.tag = .E8) →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard
        fun R _ I _ => GGExcPlusWeylModelSCr .E8 3 7 R I) := by
    intro lab hlab hs
    have hn1 : lab.n = 1 := ggQ2Exc_label_n_eq_one hlab hs.1
    have hpn : 3 ∣ 2 ^ lab.n + 1 := by rw [hn1]; norm_num
    have h0 := ggNEE_largeEvenLabelAll_model_excPlus (p := 3) Nat.prime_three (by norm_num)
      (lab := lab) (Or.inr hs.2) hpn
    rw [show ggNEE_tagOf lab.tag = .E8 by simp [ggNEE_tagOf, hs.2],
      show ggNbrExcPlusRank lab.tag = 7 by simp [ggNbrExcPlusRank, hs.2]] at h0
    exact LargeEvenLabelAll.mono (fun R _ I F h _ _ => h) h0
  have hmark := largeEvenMarking_and_labelAll_simple (S := fun lab => GGLabQTwo 3 lab ∧
      lab.tag = .E8) (P' := fun R _ I _ => GGExcPlusWeylModelSCr .E8 3 7 R I)
    hall (fun _ _ _ _ _ _ h => h.1) hL
  have hidx := ggQ2E8_index hS rfl hmark
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨R, _, I, F, -, -, -, ⟨⟨⟨hq, htag⟩, -, -⟩, -⟩⟩ :=
    largeEvenRawDatum_exists hraw
  refine ⟨lab, hq, ?_, ?_⟩
  · exact ⟨hperf, lab, hlab, largeEvenRawDatum_mono (fun R _ I F h => by
      obtain ⟨hs, hna, θ, hP⟩ := h
      exact ⟨hs, hna, θ, rfl⟩) hraw⟩
  · simpa [GGQ2LieRank, htag] using hidx

theorem ggQ2TwE6_lower
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hmarkTB : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L)
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)} :
    3 ^ 5 ≤ Nat.card (ggGamma L hN).range := by
  subst hp
  exact ggTwE6ThreeBstarRankInput_holds G 3 B Bs x L D J hS.1.1 hmarkTB hN

theorem ggQ2TwE6_upper
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hL : GGInnerDiagOnLabel (fun _ lab => GGLabQTwo p lab ∧ lab.tag = .twE6) p Bs L)
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)} :
    Nat.card (ggGamma L hN).range ≤ 3 ^ 6 := by
  subst hp
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, _, I, F, -, -, -, ⟨⟨hq, htag⟩, -, -⟩⟩ := largeEvenRawDatum_exists hraw
  have hn1 : lab.n = 1 := ggQ2Exc_label_n_eq_one hlab hq
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, hBsE, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hSst : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSst.2.2.1
  have hmul := card_range_ggGamma_mul_of (p := 3) Nat.prime_three hBsE hxBs hx1 hLx
    hSst.2.2.2.2 hN
  obtain ⟨t, r, n⟩ := lab
  have ht : t = .twE6 := htag
  subst ht
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, instF, instFin, hK, hQ⟩ := hraw
  obtain ⟨-, -, θ, hθ⟩ := hQ
  have hn1' : n = 1 := by simpa using hn1
  have hnpos : 1 ≤ n := by omega
  have hK' : Nat.card K = (2 ^ n) ^ 2 := by simpa using hK
  have hdvd : 3 ∣ 2 ^ n + 1 := by rw [hn1']; norm_num
  have hEβI : ((ggBeta L θ hN).range : Set (MulAut _)) ⊆ TwE6Delta.RecipeI K n := by
    rintro φ ⟨b, rfl⟩
    exact ggBeta_mem (L := L) (θ := θ) hN hθ.2.2 b
  have hX := ggTwE6ThreeInndiagRankInput_holds (K := K) (n := n) hnpos hK' hdvd
  have hup : Nat.card (ggBeta L θ hN).range ≤ 3 ^ 6 :=
    hX _ (isElemAbelian_range_ggBeta θ hBsE hN) hEβI
  have hcβ := card_range_ggBeta_mul_of (p := 3) Nat.prime_three hBsE hxBs hx1 hLx
    hSst.2.2.2.2 hperf θ hN
  have hAβ : Nat.card (ggGamma L hN).range = Nat.card (ggBeta L θ hN).range :=
    Nat.eq_of_mul_eq_mul_right Nat.prime_three.pos (hmul.trans hcβ.symm)
  exact hAβ.symm ▸ hup

theorem ggQ2TwE6_index {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hr : 3 ^ 5 ≤ Nat.card (ggGamma L hN).range)
    (hup : Nat.card (ggGamma L hN).range ≤ 3 ^ 6) :
    ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ 6 ∨
      ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ 5 := by
  subst hp
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, hBsE, -, -, -⟩ := hcfg.tableB_facts
  have hEA : IsElemAbelian 3 (ggGamma L hN).range :=
    isElemAbelian_range (fun a b : Bs => Subtype.ext (TableB.IsElemAbelian.comm hBsE a.2 b.2))
      (fun a : Bs => Subtype.ext (hBsE.2 a a.2)) (ggGamma L hN)
  have hA3 : IsPGroup 3 (ggGamma L hN).range :=
    fun y => ⟨1, by rw [pow_one]; exact Subtype.ext (hEA.2 y y.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA3
  have hk56 : k = 5 ∨ k = 6 := by
    have h5 : 5 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hk ▸ hr)
    have h6 : k ≤ 6 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hk ▸ hup)
    omega
  have hidx0 : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index =
      Nat.card (ggGamma L hN).range := (QTwoCav.gamma_card hN).symm
  rcases hk56 with hk5 | hk6
  · exact Or.inr (by rw [hidx0, hk, hk5])
  · exact Or.inl (by rw [hidx0, hk, hk6])

theorem ggQTwoAutomizer_four_of_twE6Full (hCav : GGQ2CavOfTBFull)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) {lab : LargeEvenLabel}
    (hM : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab))
    (hq : GGLabQTwo p lab) (htag : lab.tag = .twE6)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ GGQ2LieRank lab) :
    4 ∣ Nat.card (ggAutomizer J Bs) := by
  refine hCav hS hp ⟨lab, hq, hM, ?_⟩
  simpa [GGQ2LieRank, htag] using hidx

@[expose] def GGQ2VACLabExcNotE6TwE6 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGLabQTwo p lab ∧ (lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8)

theorem ggQ2TBFull_of_excNotE6TwE6
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hL : GGInnerDiagOnLabel GGQ2VACLabExcNotE6TwE6 p Bs L) :
    GGQ2TBFull p Bs L := by
  subst hp
  have hall : GGInnerDiagOnLabel (fun _ lab => (GGLabQTwo 3 lab ∧ lab.tag = .F4) ∨
      (GGLabQTwo 3 lab ∧ lab.tag = .E7) ∨
      (GGLabQTwo 3 lab ∧ lab.tag = .E8)) 3 Bs L := by
    refine largeEvenMarking_mono (fun lab _ _ I _ _ h => ⟨?_, h.2⟩) hL
    obtain ⟨hq, htag | htag | htag⟩ := h.1
    · exact Or.inl ⟨hq, htag⟩
    · exact Or.inr (Or.inl ⟨hq, htag⟩)
    · exact Or.inr (Or.inr ⟨hq, htag⟩)
  rcases GGInnerDiagOnLabel.elim_or (S := fun _ lab => GGLabQTwo 3 lab ∧ lab.tag = .F4)
    (T := fun _ lab => (GGLabQTwo 3 lab ∧ lab.tag = .E7) ∨
      (GGLabQTwo 3 lab ∧ lab.tag = .E8)) hall with h | h
  · exact ggQ2TBFull_of_F4 hS rfl h
  rcases GGInnerDiagOnLabel.elim_or (S := fun _ lab => GGLabQTwo 3 lab ∧ lab.tag = .E7)
    (T := fun _ lab => GGLabQTwo 3 lab ∧ lab.tag = .E8) h with h | h
  · exact ggQ2TBFull_of_E7 hS rfl h
  · exact ggQ2TBFull_of_E8 hS rfl h

theorem ggQTwoGuardFailsOn_excNotE6TwE6_of_cav
    (hCav : GGQ2CavOfTBFull) :
    GGQTwoGuardFailsOn GGQ2VACLabExcNotE6TwE6 := by
  intro G _ _ p B Bs x L D J hS hp hL
  exact hCav hS hp (ggQ2TBFull_of_excNotE6TwE6 hS hp hL)

end CFSG.StandardType

end

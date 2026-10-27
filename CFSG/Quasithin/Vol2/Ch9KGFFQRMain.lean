module

public import CFSG.Quasithin.Vol2.Ch9Sec4Facts
public import CFSG.Quasithin.Vol2.Ch9KGFFQRCase
public import CFSG.Quasithin.Vol2.Ch9KGFFQRAut
public import CFSG.Quasithin.Vol2.Ch9KGFFQRL2
public import CFSG.Quasithin.Vol2.Ch9KGFFQRL34
public import CFSG.Quasithin.Vol2.Ch9KGFFQRG24
public import CFSG.Quasithin.Background.KGSchurMult2
public import CFSG.Quasithin.Background.KGSchurMult2b
public import CFSG.Quasithin.Vol2.Ch10SecB6Prep
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Quasithin KGFF

theorem KGFF.CenterRankLe.of_eq_bot {S : Type} [Group S]
    (h : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      IsPGroup 2 ↥(Subgroup.center K) → Nonempty (K ⧸ Subgroup.center K ≃* S) →
        Subgroup.center K = ⊥) : CenterRankLe S 0 :=
  CenterRankLe.of_card_dvd fun K _ _ hK hZ he => by
    rw [h K hK hZ he, Subgroup.card_bot, pow_zero]

theorem KGFF.CenterRankLe.of_dvd_two {S : Type} [Group S]
    (h : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      IsPGroup 2 ↥(Subgroup.center K) → Nonempty (K ⧸ Subgroup.center K ≃* S) →
        Nat.card ↥(Subgroup.center K) ∣ 2) : CenterRankLe S 1 :=
  CenterRankLe.of_card_dvd fun K _ _ hK hZ he => by
    rw [pow_one]
    exact h K hK hZ he

theorem a314QuasiRankFact_of
    (hA7 : SchurMult2A7) (hL2 : SchurMult2L2Odd) (hL35 : SchurMult2L35) (hU35 : SchurMult2U35)
    (hJ1 : SchurMult2J1) (hJ2 : SchurMult2J2) (hHS : SchurMult2HS) (hRu : SchurMult2Ru)
    (hL34 : SchurMult2L34Rank) (hM22 : SchurMult2M22) (hM23 : SchurMult2M23)
    (hJ4 : SchurMult2J4) (hSp4 : SchurMult2Sp4) (hG24 : SchurMult2G24) (hD4 : SchurMult2D4)
    (hR : RankG24Fact) (hF : RankG24FrobCentFact) : A314QuasiRankFact := by
  intro G _ _ Y T B L E hSQ hO2 hT hB hTB hA5 hL hBL h314 hq hEN hE hEL hEne
  have hLY : L ≤ Y := le_of_mem_cComp hL
  have hne : modO2Image Y B ≠ modO2Image Y L := fun h =>
    hBL.ne (Vol2.Ch11.SecA.eq_of_modO2Image_eq hT hLY hBL.le (perfect_of_mem_cComp hL) hTB h)
  have hltbar : modO2Image Y B < modO2Image Y L :=
    lt_of_le_of_ne (Subgroup.map_mono fun _ hx => hBL.le hx) hne
  have hqbar := Vol2.Ch10.SecB.isQuasisimple_modO2Image hL hq
  obtain ⟨eS⟩ := nonempty_centerQuot_modO2Image hL hq
  have hS := A314Type.of_mulEquiv eS (a314Type_centerQuot hltbar hqbar h314)
  have hev : 2 ∣ Nat.card ↥L := by
    obtain ⟨e5⟩ := hA5
    have h60 : Nat.card (O2Q B) = 60 := by
      rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    have h1 : Nat.card (O2Q B) ∣ Nat.card ↥B := Subgroup.card_quotient_dvd_card _
    exact ((show 2 ∣ Nat.card (O2Q B) by rw [h60]; norm_num).trans h1).trans
      (Subgroup.card_dvd_of_le hBL.le)
  have hbound : ∀ {m r : ℕ}, AutRankLe (↥L ⧸ Subgroup.center ↥L) m →
      CenterRankLe (↥L ⧸ Subgroup.center ↥L) r → m + r ≤ 7 → rk ↥E ≤ 7 :=
    fun hA hZ hmr => (rk_le_of_autRankLe hq hEN hE hEL hA hZ).trans hmr
  have hzero : CenterRankLe (↥L ⧸ Subgroup.center ↥L) 0 → rk ↥E ≤ 7 := fun hZ =>
    absurd (inf_centralizer_eq_bot hq hE hEL hZ) hEne
  rcases hS with h | h | h | h | h | h | ⟨p, hp, hp7, h⟩ | h | h | h | h | h | h | h | h | h
  · have hZ : CenterRankLe (↥L ⧸ Subgroup.center ↥L) 2 := fun K _ _ hK hZ ⟨e⟩ E₀ h1 h2 =>
      (hL34 K hK hZ (IsPSL.of_mulEquiv e.symm h) E₀ h1 h2).trans (by norm_num)
    have h1 := rk_le_four_add_of_l34 hq hev h hEN hE
    have h2 := rk_inf_centralizer_le hq hE hEL hZ
    omega
  · exact hzero (CenterRankLe.of_eq_bot fun K _ _ hK hZ ⟨e⟩ =>
      hSp4 2 K hK hZ (IsPSp4.of_mulEquiv e.symm h))
  · exact hbound (autRankLe_g24 hR hF h) (CenterRankLe.of_dvd_two fun K _ _ hK hZ ⟨e⟩ =>
      hG24 K hK hZ (IsG2.of_mulEquiv e.symm h)) (by norm_num)
  · exact hzero (CenterRankLe.of_eq_bot fun K _ _ hK hZ ⟨e⟩ =>
      hD4 2 K hK hZ (Is3D4.of_mulEquiv e.symm h))
  · obtain ⟨e7⟩ := h
    exact hbound (AutRankLe.of_mulEquiv e7 autRankLe_alt7)
      (CenterRankLe.of_dvd_two fun K _ _ hK hZ ⟨e⟩ => hA7 K hK hZ ⟨e.trans e7⟩) (by norm_num)
  · exact hbound (autRankLe_of_psl2_25 h) (CenterRankLe.of_dvd_two fun K _ _ hK hZ ⟨e⟩ =>
      hL2 5 2 (by norm_num) K hK hZ (IsPSL.of_mulEquiv e.symm h)) (by norm_num)
  · exact hbound (autRankLe_psl2_prime hp hp7 h) (CenterRankLe.of_dvd_two fun K _ _ hK hZ ⟨e⟩ =>
      hL2 p 1 (by omega) K hK hZ (IsPSL.of_mulEquiv e.symm h)) (by norm_num)
  · exact hzero (CenterRankLe.of_eq_bot fun K _ _ hK hZ ⟨e⟩ =>
      hL35 K hK hZ (IsPSL.of_mulEquiv e.symm h))
  · exact hzero (CenterRankLe.of_eq_bot fun K _ _ hK hZ ⟨e⟩ =>
      hU35 K hK hZ (IsPSU.of_mulEquiv e.symm h))
  · exact hbound (autRankLe_of_m22 h) (CenterRankLe.of_cyclic fun K _ _ hK hZ ⟨e⟩ =>
      (hM22 K hK hZ (IsSporadic.of_mulEquiv e.symm h)).1) (by norm_num)
  · exact hzero (CenterRankLe.of_eq_bot fun K _ _ hK hZ ⟨e⟩ =>
      hM23 K hK hZ (IsSporadic.of_mulEquiv e.symm h))
  · exact hzero (CenterRankLe.of_eq_bot fun K _ _ hK hZ ⟨e⟩ =>
      hJ1 K hK hZ (IsSporadic.of_mulEquiv e.symm h))
  · exact hbound (autRankLe_of_j2 h) (CenterRankLe.of_dvd_two fun K _ _ hK hZ ⟨e⟩ =>
      hJ2 K hK hZ (IsSporadic.of_mulEquiv e.symm h)) (by norm_num)
  · exact hzero (CenterRankLe.of_eq_bot fun K _ _ hK hZ ⟨e⟩ =>
      hJ4 K hK hZ (IsSporadic.of_mulEquiv e.symm h))
  · exact hbound (autRankLe_of_hs h) (CenterRankLe.of_dvd_two fun K _ _ hK hZ ⟨e⟩ =>
      hHS K hK hZ (IsSporadic.of_mulEquiv e.symm h)) (by norm_num)
  · exact hbound (autRankLe_ru h) (CenterRankLe.of_dvd_two fun K _ _ hK hZ ⟨e⟩ =>
      hRu K hK hZ (IsSporadic.of_mulEquiv e.symm h)) (by norm_num)

end CFSG.Quasithin.H13.Ch9

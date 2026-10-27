module

public import CFSG.LocalAnalysis.StandardType.GGKD2SmallPieces1615
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA6
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOrders
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQSz
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Alternating.Multipliers.Small
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BSurjInputs
public import Certificates.Certificate10027
public import Certificates.Certificate10095
public import Certificates.Certificate10095Base
public import Certificates.Certificate10100
public import Certificates.Certificate10101
public import Certificates.Certificate10102
public import Certificates.Certificate10104
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate2051
public import Certificates.Certificate2053
public import Certificates.Certificate2056
public import Certificates.Certificate2057
public import Certificates.Certificate2058
public import Certificates.Certificate2130
public import Certificates.Certificate2135
public import Certificates.Certificate2136
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2145
public import Certificates.Certificate9201

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615

private lemma ltrke2_card_of_label_A13 {X : Type} [Group X]
    (h : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) X) : Nat.card X = 504 := by
  unfold GGHasLabel at h
  simp only [LargeEvenRawDatum, LargeEvenRecipeLinear] at h
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e0⟩⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  rw [Nat.card_congr e0.toEquiv]
  have hStated : Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)) =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
    rw [largeEvenProj_eq_statedProj, largeEvenSLGroup_eq_statedSL]
    exact Nat.card_congr
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.toEquiv
  rw [hStated, CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear K 2 (by norm_num),
    hKcard]
  norm_num

private lemma ltrke2_not_seven_dvd_of_label_B2der {R : Type} [Group R]
    (h : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) R) : ¬ 7 ∣ Nat.card R := by
  obtain ⟨e⟩ := ggB2der_label_iso_A6 h
  rw [Nat.card_congr e.toEquiv, CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 4]
  norm_num

private lemma ltrke2_not_seven_dvd_of_label_twF4der
    {R : Type} [Group R]
    (h : GGHasLabel (⟨.twF4der, 0, 1⟩ : LargeEvenLabel) R) : ¬ 7 ∣ Nat.card R := by
  unfold GGHasLabel at h
  simp only [LargeEvenRawDatum, LargeEvenRecipeTwF4] at h
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e0⟩⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hTits : CFSG.Blueprint.ReeTitsModel
      (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl,
      reeTitsRelationModel_largeEven 0 hKcard⟩
  have hne : ¬ 7 ∣ Nat.card (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) :=
    CFSG.EvenSmallLie.Child3.not_seven_dvd_of_reeTitsModel_Tits hTits
  intro h7
  rw [Nat.card_congr e0.toEquiv] at h7
  exact hne h7

private lemma ltrke2_not_three_dvd_of_label_twB2
    {R : Type} [Group R] {n : ℕ} (ha : 1 ≤ (n - 1) / 2)
    (h : GGHasLabel (⟨.twB2, 0, n⟩ : LargeEvenLabel) R) : ¬ 3 ∣ Nat.card R := by
  unfold GGHasLabel at h
  simp only [LargeEvenRawDatum, LargeEvenRecipeSuzuki] at h
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e0⟩⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.FQ.nonempty_szQuot_equiv ha hKcard
  have hmodel : CFSG.Blueprint.SuzukiModel R 2 (2 * ((n - 1) / 2) + 1) :=
    ⟨rfl, (n - 1) / 2, ha, K, hKf, hKfin, rfl, hKcard, ⟨e0.trans e1⟩⟩
  exact CFSG.RankThree.PartTwo.KFacts.KP7.three_not_dvd_card hmodel

private lemma ltrke2_centerQuot_card_dvd {L' R : Type} [Group L'] [Group R]
    (ψ : L' →* R) (hker : ψ.ker ≤ Subgroup.center L') (J : Subgroup L') :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card ↥(J.map ψ) := by
  have hsub : (ψ.comp J.subtype).ker ≤ Subgroup.center J := by
    intro j hj
    have hjker : (j : L') ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      simpa using hj
    have hjZ : (j : L') ∈ Subgroup.center L' := hker hjker
    rw [Subgroup.mem_center_iff] at hjZ ⊢
    intro x
    exact Subtype.ext (hjZ (x : L'))
  calc Nat.card (↥J ⧸ Subgroup.center ↥J)
      ∣ Nat.card (↥J ⧸ (ψ.comp J.subtype).ker) := Subgroup.index_dvd_of_le hsub
    _ = Nat.card ↥(J.map ψ) := by
        have hrange : (ψ.comp J.subtype).range = J.map ψ := by
          ext r
          constructor
          · rintro ⟨j, rfl⟩
            exact ⟨j, j.2, rfl⟩
          · rintro ⟨j, hj, rfl⟩
            exact ⟨⟨j, hj⟩, rfl⟩
        rw [← hrange]
        exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (ψ.comp J.subtype)).toEquiv

private lemma ltrke2_setupFalse_of_no_dvd {R : Type} [Group R] {I : Set (MulAut R)}
    {p : ℕ} (hp : p ∣ 504) (hnot : ¬ p ∣ Nat.card R) : SetupFalse R I := by
  intro L' _ _ ψ hsurj hker hcomm e J a hsetup
  unfold GGRankOneSetup at hsetup
  obtain ⟨-, -, -, -, -, -, -, hJlabel, -, -, -, -⟩ := hsetup
  have h504eq : Nat.card (↥J ⧸ Subgroup.center ↥J) = 504 := ltrke2_card_of_label_A13 hJlabel
  have hdvd : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card R :=
    (ltrke2_centerQuot_card_dvd ψ hker J).trans (Subgroup.card_subgroup_dvd_card (J.map ψ))
  exact hnot (hp.trans (h504eq ▸ hdvd))

theorem smallDerivedSuzuki_holds :
    SmallDerivedSuzuki := by
  intro lab hlab htag
  rcases htag with ht | ht | ht
  ·
    obtain ⟨t, l, n⟩ := lab
    obtain rfl : t = .B2der := ht
    obtain ⟨-, hl, hn⟩ := hlab
    subst hl
    subst hn
    intro Q hQ
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    refine ⟨K, hKf, hKfin, hKcard, hq, ?_⟩
    have hGLB : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel)
        (LargeEvenProj (⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)) :=
      ⟨K, hKf, hKfin, hKcard, ⟨MulEquiv.refl _⟩⟩
    exact ltrke2_setupFalse_of_no_dvd (p := 7) (by norm_num)
      (ltrke2_not_seven_dvd_of_label_B2der hGLB)
  ·
    obtain ⟨t, l, n⟩ := lab
    obtain rfl : t = .twF4der := ht
    obtain ⟨-, hl, hn⟩ := hlab
    subst hl
    subst hn
    intro Q hQ
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwF4] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    refine ⟨K, hKf, hKfin, hKcard, hq, ?_⟩
    have hGLF : GGHasLabel (⟨.twF4der, 0, 1⟩ : LargeEvenLabel)
        (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) :=
      ⟨K, hKf, hKfin, hKcard, ⟨MulEquiv.refl _⟩⟩
    exact ltrke2_setupFalse_of_no_dvd (p := 7) (by norm_num)
      (ltrke2_not_seven_dvd_of_label_twF4der hGLF)
  ·
    obtain ⟨t, l, n⟩ := lab
    obtain rfl : t = .twB2 := ht
    obtain ⟨-, hl, -, h3⟩ := hlab
    subst hl
    have ha : 1 ≤ (n - 1) / 2 := by
      have h3' : 3 ≤ n := by simpa using h3
      rw [Nat.one_le_div_iff (by norm_num : 0 < 2)]
      omega
    intro Q hQ
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeSuzuki] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    refine ⟨K, hKf, hKfin, hKcard, hq, ?_⟩
    have hGLB : GGHasLabel (⟨.twB2, 0, n⟩ : LargeEvenLabel)
        (LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K)) :=
      ⟨K, hKf, hKfin, hKcard, ⟨MulEquiv.refl _⟩⟩
    exact ltrke2_setupFalse_of_no_dvd (p := 3) (by norm_num)
      (ltrke2_not_three_dvd_of_label_twB2 ha hGLB)

end CFSG.StandardType.KD2Pieces1615

end

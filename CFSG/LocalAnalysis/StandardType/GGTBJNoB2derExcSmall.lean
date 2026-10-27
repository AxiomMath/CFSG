module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA1
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA6
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestG2
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
public import CFSG.LocalAnalysis.StandardType.MarkingSmall
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.RankThree.PartOne.SEITZ8.D4Order

public section

namespace CFSG.StandardType.S2MathAs4B2der1822

open CFSG CFSG.Assembly

private theorem a1sm_card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem a1sm_dvd_of_label {R : Type} [Group R] {p : ℕ} (hp : p ∣ 360)
    (h : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) R) : p ∣ Nat.card R := by
  obtain ⟨e⟩ := ggB2der_label_iso_A6 h
  rw [Nat.card_congr e.toEquiv, a1sm_card_alt6]
  exact hp

private theorem a1sm_false_of_not_dvd {R : Type} [Group R] {p : ℕ} (hp : p ∣ 360)
    (hnot : ¬ p ∣ Nat.card R) {J : Subgroup R}
    (hJ : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) : False :=
  hnot ((a1sm_dvd_of_label hp hJ).trans
    ((Subgroup.card_quotient_dvd_card (Subgroup.center ↥J)).trans
      (Subgroup.card_subgroup_dvd_card J)))

private theorem a1sm_b2der_false {R : Type} [Group R] [Finite R] (hcardR : Nat.card R = 360)
    {φ : MulAut R} (hφ : φ ≠ 1) {J : Subgroup R} (hJle : J ≤ ggFixSub φ)
    (hJ : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) : False := by
  have hJZ : Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
    obtain ⟨e⟩ := ggB2der_label_iso_A6 hJ
    rw [Nat.card_congr e.toEquiv, a1sm_card_alt6]
  have hJcard : Nat.card J = 360 * Nat.card (Subgroup.center ↥J) := by
    rw [← hJZ, Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)]
  have hJdvd : Nat.card J ∣ Nat.card R := Subgroup.card_subgroup_dvd_card J
  have hJleR : Nat.card J ≤ 360 := by
    rw [hcardR] at hJdvd
    exact Nat.le_of_dvd (by norm_num) hJdvd
  have hc : Nat.card (Subgroup.center ↥J) = 1 := by
    have hc1 : 1 ≤ Nat.card (Subgroup.center ↥J) := Nat.card_pos
    rw [hJcard] at hJleR
    omega
  have hJeq : Nat.card J = Nat.card R := by
    rw [hJcard, hc, mul_one, hcardR]
  have htop : J = ⊤ := Subgroup.eq_top_of_card_eq J hJeq
  have hfix : ggFixSub φ = ⊤ := by
    have hle : (⊤ : Subgroup R) ≤ ggFixSub φ := htop ▸ hJle
    exact top_le_iff.mp hle
  exact hφ (by
    refine MulEquiv.ext fun x => ?_
    have hx : x ∈ ggFixSub φ := by rw [hfix]; exact Subgroup.mem_top x
    simpa using hx)

private theorem a1sm_not_three_dvd_suzuki (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq3 : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hq1' : (2 ^ (2 * a + 1) - 1) % 3 = 1 := by omega
  have hsq : (2 ^ (2 * a + 1)) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq3]
  have hsq1 : ((2 ^ (2 * a + 1)) ^ 2 + 1) % 3 = 2 := by omega
  have h1 : (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) % 3 = 1 := by
    rw [Nat.mul_mod, hsq, hq1']
  have h2 : (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1) % 3 = 2 := by
    rw [Nat.mul_mod, h1, hsq1]
  omega

theorem noB2derInput_twB2 :
    SimpleNoB2derInput fun lab => lab.tag = .twB2 := by
  intro lab _ htag
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  intro _ _ _ _ J _ hJlabel
  have hnot : ¬ 3 ∣ Nat.card (LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K)) := by
    have hnotSz : ¬ 3 ∣ Nat.card ↥(LargeEvenSzGroup ((n - 1) / 2) K) := by
      rw [largeEvenSzGroup_eq]
      rw [CFSG.LieType.Ree.suzuki_order (a := (n - 1) / 2) (K := K) hK]
      exact a1sm_not_three_dvd_suzuki ((n - 1) / 2)
    exact fun h3 => hnotSz (h3.trans
      (Subgroup.card_quotient_dvd_card (Subgroup.center ↥(LargeEvenSzGroup ((n - 1) / 2) K))))
  exact a1sm_false_of_not_dvd (by norm_num : 3 ∣ 360) hnot hJlabel

theorem noB2derInput_B2der : SimpleNoB2derInput fun lab => lab.tag = .B2der := by
  intro lab _ htag
  refine largeEvenLabelAll_b2der htag ?_
  intro K _ _ hK
  intro φ hφ _ _ J hJcomp hJlabel
  have hcardR : Nat.card (LargeEvenProj
      (⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ :
        Subgroup (GL (Fin 2 ⊕ Fin 2) K))) = 360 := by
    obtain ⟨e⟩ := nonempty_b2der_equiv_alternatingGroup hK
    rw [Nat.card_congr e.toEquiv, a1sm_card_alt6]
  exact a1sm_b2der_false hcardR hφ hJcomp.1 hJlabel

theorem noB2derInput_G2der :
    SimpleNoB2derInput fun lab => lab.tag = .G2der := by
  intro lab _ htag
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  intro _ _ _ _ J _ hJlabel
  have hnot : ¬ 5 ∣ Nat.card
      (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) := by
    obtain ⟨e⟩ := TableBExcSmallRest.nonempty_g2der_equiv_su3 K hK
    rw [Nat.card_congr e.toEquiv]
    rw [CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU CFSG.Quasithin.G2U.card_F9]
    norm_num
  exact a1sm_false_of_not_dvd (by norm_num : 5 ∣ 360) hnot hJlabel

theorem noB2derInput_triD4_two :
    SimpleNoB2derInput fun lab => lab.tag = .triD4 ∧ lab.n = 1 := by
  intro lab _ hP
  obtain ⟨htag, hn⟩ := hP
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn
  subst htag
  subst hn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  intro _ _ _ _ J _ hJlabel
  have hnot : ¬ 5 ∣ Nat.card
      (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 1)) := by
    haveI : CharP K 2 := by
      haveI : Fintype K := Fintype.ofFinite K
      refine charP_of_card_eq_prime_pow (p := 2) (f := 3) ?_
      rw [← Nat.card_eq_fintype_card, hK]
      norm_num
    set σ := iterateFrobeniusEquiv K 2 1 with hσdef
    have hσ : ∀ c, σ c = c ^ 2 ^ 1 := fun c => by
      rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
    obtain ⟨e⟩ := TableBExcSmallRest.nonempty_triD4_equiv (n := 1) le_rfl K hK σ hσ
    rw [Nat.card_congr e.toEquiv]
    rw [CFSG.RankThree.PartOne.SEITZ8.card_graphFixedRootGroup_D4_orient (K := K)
      (f := 1) (r := 1) le_rfl (Or.inl rfl) hK σ.toRingHom (fun c => by simpa using hσ c)]
    norm_num [CFSG.Open.ordTrialityD4]
  exact a1sm_false_of_not_dvd (by norm_num : 5 ∣ 360) hnot hJlabel

end CFSG.StandardType.S2MathAs4B2der1822

end

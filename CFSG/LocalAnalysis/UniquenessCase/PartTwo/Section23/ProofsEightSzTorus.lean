module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightSzDiagonalTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Nb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem ncard_conjSetOf_eq_two {D : Data G} {Ch : Choice2011 G}
    (h2115 : S21_15N D Ch) (hsig : D.sig.Nonempty) (h1930 : H1930 D)
    (c : Ctx23L D Ch) {K : Subgroup G} (hK : K ∈ calC D.M) {a : ℕ} (hSz : IsSz (Bar2 K) a)
    (hne : conjClosure D.M K ≠ K) : (conjSetOf D.M K).ncard = 2 := by
  classical
  have hodd_a : Odd a := CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hSz
  have ha3 : 3 ≤ a := CFSG.LocalAnalysis.EvenBN.GMSK.three_le_of_lieModel_twistedB2 hSz
  have hne1 : 2 ^ a - 1 ≠ 1 := by
    have h8 : 8 ≤ 2 ^ a := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha3
    omega
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne1
  have hrdvdBar2 : r ∣ Nat.card (Bar2 K) := hrdvd.trans (uc22ine229_dvd_card_of_isSz hSz)
  have hrdvdK : r ∣ Nat.card K := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)]
    exact dvd_mul_of_dvd_left hrdvdBar2 _
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) r hrdvdK
  let A : Subgroup G := Subgroup.zpowers (y : G)
  have hAcard : Nat.card A = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hyord]
  have hAK : A ≤ K := Subgroup.zpowers_le.mpr y.2
  obtain ⟨p, hp⟩ := hsig
  have hconj := h2115 h1930 c.withB0.toCtx23.toCtx21 K hK a (Or.inr hSz) hne a hodd_a
    dvd_rfl r hr hrdvd p hp A hAcard hAK
  exact hconj.2.1

private theorem exists_t_not_normalizer {D : Data G} {K : Subgroup G}
    (hc2 : (conjSetOf D.M K).ncard = 2) :
    ∃ t ∈ D.T, K.map (MulAut.conj t).toMonoidHom ≠ K := by
  by_contra h
  push Not at h
  have hTK : D.T ≤ Subgroup.normalizer (K : Set G) := fun t ht =>
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (h t ht)
  have hnot := uc22p22a_not_two_dvd_ncard D.sylowM hTK
  rw [hc2] at hnot
  norm_num at hnot

private theorem exists_diagonal_torus_data {D : Data G} {K : Subgroup G}
    (hBor : KSzBorel) (hAut : KSzTwoAut) (hK : K ∈ calC D.M) {a : ℕ} (hSz : IsSz (Bar2 K) a)
    (hc2 : (conjSetOf D.M K).ncard = 2) {t : G} (htT : t ∈ D.T)
    (htK : K.map (MulAut.conj t).toMonoidHom ≠ K) :
    ∃ (r : ℕ) (h : G) (d : xbar K), r.Prime ∧ r ∣ 2 ^ a - 1 ∧ r ≠ 2 ∧
      h ∈ conjClosure D.M K ∧
      h ∈ Subgroup.normalizer (D.T : Set G) ∧ h ∈ Subgroup.normalizer (K : Set G) ∧
      orderOf h = r ∧ d ∈ Subgroup.normalizer ((sylowImage D K : Set (xbar K))) ∧
      d ∉ sylowImage D K ∧
      (∀ hh : h ∈ Subgroup.normalizer (K : Set G),
        inducedQuotInfAut K h hh = MulAut.conj d) ∧
      Function.Injective (MulAut.conj : xbar K →* MulAut (xbar K)) := by
  obtain ⟨r, h, d, hr, hrdvd, hr2, hhR, hhT, hhK, hhord, hdN, hdS, hθ⟩ :=
    Ctx23L.exists_diagonal_torus_elem hBor hAut hK hSz hc2 htT htK
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  have hZ : Subgroup.center (xbar K) = ⊥ := by
    obtain ⟨e⟩ := uc22p21k_quotCenter_equiv (center_barInf_eq_bot hq)
    exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e (center_barInf_eq_bot hq)
  exact ⟨r, h, d, hr, hrdvd, hr2, hhR, hhT, hhK, hhord, hdN, hdS, hθ,
    P22y.conj_injective_of_center_eq_bot hZ⟩

private theorem orderOf_diagonal_eq_prime {D : Data G} {K : Subgroup G} {r : ℕ} {h : G}
    {d : xbar K} (hr : r.Prime) (hhK : h ∈ Subgroup.normalizer (K : Set G))
    (hhord : orderOf h = r) (hdS : d ∉ sylowImage D K)
    (hθ : ∀ hh : h ∈ Subgroup.normalizer (K : Set G),
      inducedQuotInfAut K h hh = MulAut.conj d)
    (hconj_inj : Function.Injective (MulAut.conj : xbar K →* MulAut (xbar K))) :
    orderOf d = r := by
  have hθh : inducedQuotInfAut K h hhK = MulAut.conj d := hθ hhK
  have hθr : (inducedQuotInfAut K h hhK) ^ r = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    exact (orderOf_inducedQuotInfAut_dvd K hhK).trans (by rw [hhord])
  have hdr : (MulAut.conj d) ^ r = 1 := by rw [← hθh]; exact hθr
  have hdvd : orderOf d ∣ r := by
    apply orderOf_dvd_of_pow_eq_one
    apply hconj_inj
    rw [map_pow, hdr, map_one]
  rcases (Nat.dvd_prime hr).mp hdvd with h1 | h1
  · exfalso
    rw [orderOf_eq_one_iff.mp h1] at hdS
    exact hdS (sylowImage D K).one_mem
  · exact h1

private theorem diagonal_torus_zpowers {D : Data G} {K : Subgroup G} {r : ℕ} {h : G}
    (hK : K ∈ calC D.M) (hr : r.Prime) (hr2 : r ≠ 2)
    (hhR : h ∈ conjClosure D.M K) (hhT : h ∈ Subgroup.normalizer (D.T : Set G))
    (hhK : h ∈ Subgroup.normalizer (K : Set G)) (hhord : orderOf h = r) :
    Subgroup.zpowers h ≠ ⊥ ∧ Odd (Nat.card (Subgroup.zpowers h)) ∧
      Subgroup.zpowers h ≤ D.M ∧
      Subgroup.zpowers h ≤ Subgroup.normalizer (D.T : Set G) ∧
      Subgroup.zpowers h ≤ Subgroup.normalizer (K : Set G) := by
  have hAcard : Nat.card (Subgroup.zpowers h) = r := by rw [Nat.card_zpowers, hhord]
  have hAne : Subgroup.zpowers h ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hAcard
    exact hr.ne_one hAcard.symm
  have hAodd : Odd (Nat.card (Subgroup.zpowers h)) := by
    rw [hAcard]
    exact hr.odd_of_ne_two hr2
  have hAM : Subgroup.zpowers h ≤ D.M :=
    (Subgroup.zpowers_le.mpr hhR).trans
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree.conjClosure_le hK.1.le)
  exact ⟨hAne, hAodd, hAM,
    Subgroup.zpowers_le.mpr hhT, Subgroup.zpowers_le.mpr hhK⟩

private theorem zpow_mem_normalizer_not_mem_sylowImage {D : Data G} {K : Subgroup G}
    {r : ℕ} {d : xbar K} (hr : r.Prime) (hr2 : r ≠ 2)
    (hS2 : IsPGroup 2 (sylowImage D K))
    (hdN : d ∈ Subgroup.normalizer ((sylowImage D K : Set (xbar K))))
    (hconjord : orderOf (MulAut.conj d) = r) {n : ℤ}
    (hcop : Nat.Coprime r n.natAbs) :
    d ^ n ∈ Subgroup.normalizer ((sylowImage D K : Set (xbar K))) ∧
      d ^ n ∉ sylowImage D K := by
  refine ⟨Subgroup.zpow_mem _ hdN n, ?_⟩
  intro hmem
  obtain ⟨k, hk⟩ := hS2 ⟨d ^ n, hmem⟩
  have horddn : orderOf (MulAut.conj (d ^ n)) = r := by
    rw [map_zpow, orderOf_zpow, hconjord, hcop.gcd_eq_one, Nat.div_one]
  have hk1 : orderOf (⟨d ^ n, hmem⟩ : ↥(sylowImage D K)) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one hk
  have hk2 : orderOf (d ^ n : xbar K) ∣ 2 ^ k := by simpa using hk1
  have hk3 : orderOf (MulAut.conj (d ^ n)) ∣ orderOf (d ^ n : xbar K) :=
    orderOf_map_dvd (MulAut.conj : xbar K →* MulAut (xbar K)) (d ^ n)
  have hdvd : r ∣ 2 ^ k := horddn ▸ (hk3.trans hk2)
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd))

private theorem exists_conj_zpow_inducedQuotInfAut {D : Data G} {K : Subgroup G}
    {r : ℕ} {h : G} {d : xbar K} (hr : r.Prime) (hr2 : r ≠ 2)
    (hS2 : IsPGroup 2 (sylowImage D K))
    (hhK : h ∈ Subgroup.normalizer (K : Set G)) (hhord : orderOf h = r)
    (hdN : d ∈ Subgroup.normalizer ((sylowImage D K : Set (xbar K))))
    (hdord : orderOf d = r)
    (hθ : ∀ hh : h ∈ Subgroup.normalizer (K : Set G),
      inducedQuotInfAut K h hh = MulAut.conj d)
    (hconj_inj : Function.Injective (MulAut.conj : xbar K →* MulAut (xbar K))) :
    ∀ x ∈ Subgroup.zpowers h, ∀ hx : x ∈ Subgroup.normalizer (K : Set G), x ≠ 1 →
      ∃ d' ∈ Subgroup.normalizer ((sylowImage D K : Set (xbar K))),
        d' ∉ sylowImage D K ∧ inducedQuotInfAut K x hx = MulAut.conj d' := by
  intro x hx hxK hxne
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hθpow : inducedQuotInfAut K (h ^ n) hxK =
      (inducedQuotInfAut K h hhK) ^ n := by
    change inducedQuotInfAutHom K ⟨h ^ n, hxK⟩ =
      (inducedQuotInfAutHom K ⟨h, hhK⟩) ^ n
    rw [← map_zpow]
    congr 1
  have hθh : inducedQuotInfAut K h hhK = MulAut.conj d := hθ hhK
  have hconjord : orderOf (MulAut.conj d) = r := by
    rw [← hdord]
    exact orderOf_injective (MulAut.conj : xbar K →* MulAut (xbar K)) hconj_inj d
  have hdiv : ¬ (r : ℤ) ∣ n := by
    intro hdvd
    apply hxne
    rw [zpow_eq_one_iff_modEq, hhord, Int.modEq_zero_iff_dvd]
    exact hdvd
  have hcop : Nat.Coprime r n.natAbs := by
    refine (hr.coprime_iff_not_dvd).2 fun hdvd => hdiv ?_
    exact (Int.natCast_dvd).mpr hdvd
  obtain ⟨hdnN, hdnS⟩ :=
    zpow_mem_normalizer_not_mem_sylowImage hr hr2 hS2 hdN hconjord hcop
  exact ⟨d ^ n, hdnN, hdnS, by rw [hθpow, hθh, map_zpow]⟩

theorem Ctx23L.exists_szTorus {D : Data G} {Ch : Choice2011 G}
    (h2115 : S21_15N D Ch) (hsig : D.sig.Nonempty) (h1930 : H1930 D) (hBor : KSzBorel)
    (hAut : KSzTwoAut) (c : Ctx23L D Ch) {K : Subgroup G} (hK : K ∈ calC D.M) {a : ℕ}
    (hSz : IsSz (Bar2 K) a) (hne : conjClosure D.M K ≠ K) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ a - 1 ∧ ∃ A : Subgroup G, Nat.card A = r ∧ A ≠ ⊥ ∧
      Odd (Nat.card A) ∧ A ≤ D.M ∧
      A ≤ Subgroup.normalizer (D.T : Set G) ∧ A ≤ Subgroup.normalizer (K : Set G) ∧
      ∀ x ∈ A, ∀ hx : x ∈ Subgroup.normalizer (K : Set G), x ≠ 1 →
        ∃ d ∈ Subgroup.normalizer ((sylowImage D K : Set (xbar K))),
          d ∉ sylowImage D K ∧ inducedQuotInfAut K x hx = MulAut.conj d := by
  classical
  have hc2 := ncard_conjSetOf_eq_two h2115 hsig h1930 c hK hSz hne
  obtain ⟨t, htT, htK⟩ := exists_t_not_normalizer (D := D) (K := K) hc2
  obtain ⟨r, h, d, hr, hrdvd, hr2, hhR, hhT, hhK, hhord, hdN, hdS, hθ, hconj_inj⟩ :=
    exists_diagonal_torus_data hBor hAut hK hSz hc2 htT htK
  have hS2 : IsPGroup 2 (sylowImage D K) :=
    (isSylowOf_map_piBarInf (D := D) (K := K) hK).isPGroup
  obtain ⟨hAne, hAodd, hAM, hAT, hAK⟩ :=
    diagonal_torus_zpowers hK hr hr2 hhR hhT hhK hhord
  have hAcard : Nat.card (Subgroup.zpowers h) = r := by
    rw [Nat.card_zpowers, hhord]
  have hdord := orderOf_diagonal_eq_prime hr hhK hhord hdS hθ hconj_inj
  exact ⟨r, hr, hrdvd, Subgroup.zpowers h, hAcard, hAne, hAodd, hAM, hAT, hAK,
    exists_conj_zpow_inducedQuotInfAut hr hr2 hS2 hhK hhord hdN hdord hθ hconj_inj⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

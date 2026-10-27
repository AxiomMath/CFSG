module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentySixOmega
import CFSG.GroupTheory.PGroupFixedPointCongruence
public import CFSG.Quasithin.Vol2.Ch1Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem thirteen_not_dvd_two_pow_sub_one {m : ℕ} (hm : Odd m) : ¬ 13 ∣ 2 ^ m - 1 := by
  intro hdvd
  have hcast : ((2 ^ m - 1 : ℕ) : ZMod 13) = 0 :=
    (ZMod.natCast_eq_zero_iff (2 ^ m - 1) 13).mpr hdvd
  have h2pow : (2 : ZMod 13) ^ m = 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one] at hcast
    exact sub_eq_zero.mp hcast
  have hord : orderOf (2 : ZMod 13) = 12 := by
    rw [orderOf_eq_iff (by norm_num : 0 < 12)]
    refine ⟨by decide, ?_⟩
    intro k hk _
    interval_cases k <;> decide
  have h12 : 12 ∣ m := by
    rw [← hord]
    exact orderOf_dvd_iff_pow_eq_one.mpr h2pow
  obtain ⟨k, rfl⟩ := hm
  omega

theorem exists_prime_dvd_two_pow_sub_one_ne_thirteen {m : ℕ} (hm : 2 ≤ m) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ m - 1 ∧ r ≠ 13 := by
  rcases Nat.even_or_odd m with he | ho
  · exact ⟨3, Nat.prime_three, uc22s13xo_three_dvd_sub_one he, by norm_num⟩
  · have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    norm_num at h4
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (n := 2 ^ m - 1) (by omega)
    exact ⟨r, hr, hrd, fun h13 => thirteen_not_dvd_two_pow_sub_one ho (h13 ▸ hrd)⟩

theorem false_of_three_pow_modEq_one {r d : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr13 : r ≠ 13)
    (hd1 : 1 ≤ d) (hd3 : d ≤ 3) (h : 3 ^ d ≡ 1 [MOD r]) : False := by
  have hdvd : r ∣ 3 ^ d - 1 := h.symm.dvd'
  have h2 : ¬ r ∣ 2 := fun h' => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h')
  interval_cases d
  · exact h2 (by simpa using hdvd)
  · have h8 : r ∣ 2 ^ 3 := by norm_num at hdvd ⊢; exact hdvd
    exact h2 (hr.dvd_of_dvd_pow h8)
  · have h26 : r ∣ 2 * 13 := by norm_num at hdvd ⊢; exact hdvd
    rcases hr.dvd_mul.mp h26 with h' | h'
    · exact h2 h'
    · exact hr13 ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h')

theorem Ctx23L.exists_mem_B0_not_mem_centralizer_Z_of_dvd {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h53 : S23_5_3 D Ch) (h1930 : H1930 D)
    (hm1 : 1 ≤ CFSG.Open.pRank 2 D.Z) (hmdvd : CFSG.Open.pRank 2 D.Z ∣ c.n)
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ 2 ^ CFSG.Open.pRank 2 D.Z - 1) :
    ∃ b ∈ c.B0, orderOf b = r ∧ b ∉ Subgroup.centralizer (D.Z : Set G) := by
  classical
  set m := CFSG.Open.pRank 2 D.Z with hm
  have hr_pi : r ∈ piSet c.B0 := by
    rw [c.hpi]
    exact ⟨hr, hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one (x := 2) hmdvd)⟩
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨b, hbo⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) r hr_pi.2
  have hboG : orderOf (b : G) = r := by rw [Subgroup.orderOf_coe, hbo]
  refine ⟨(b : G), b.2, hboG, ?_⟩
  rintro hbC
  have hbZ : (b : G) ∈ c.B0 ⊓ Subgroup.centralizer (D.Z : Set G) := ⟨b.2, hbC⟩
  let c₀ : Ctx23L D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  rcases h53 h1930 c₀ c₀.hpi with hbot | ⟨-, hpiZ⟩
  · have hb1 : (b : G) = 1 := by
      have hmem : (b : G) ∈ (⊥ : Subgroup G) := hbot ▸ hbZ
      simpa using hmem
    exact hr.ne_one (by rw [← hboG, hb1, orderOf_one])
  · have hr_Z : r ∈ piSet (c₀.B ⊓ Subgroup.centralizer (D.Z : Set G)) :=
      ⟨hr, by rw [← hboG]; exact Subgroup.orderOf_dvd_natCard _ hbZ⟩
    have hplus : r ∣ 2 ^ m + 1 := (hpiZ ▸ hr_Z).2
    have htwo : r ∣ 2 := by
      have hsub := Nat.dvd_sub hplus hrdvd
      rwa [show (2 ^ m + 1) - (2 ^ m - 1) = 2 by
        have := Nat.one_le_two_pow (n := m); omega] at hsub
    exact (CFSG.GroupTheory.SuzukiTwoGroup.odd_two_pow_sub_one (by omega)).not_two_dvd_nat
      ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp htwo ▸ hrdvd)

theorem exists_bar2_normal_noncyclic_exponent_classTwo {M : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hnc : ¬ IsCyclic ↥(CFSG.pCore q (Bar2 M))) :
    ∃ Dbar : Subgroup (Bar2 M), Dbar.Normal ∧ IsPGroup q ↥Dbar ∧ Dbar ≠ ⊥ ∧
      ¬ IsCyclic ↥Dbar ∧ (∀ y ∈ Dbar, y ^ q = 1) ∧ ⁅⁅Dbar, Dbar⁆, Dbar⁆ = ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hQp : IsPGroup q (CFSG.pCore q (Bar2 M)) := CFSG.pCore_isPGroup
  have hQn : (CFSG.pCore q (Bar2 M)).Normal := CFSG.pCore_normal
  obtain ⟨Dbar, hle, hne, hDnc, hexp, hcl, hnorm⟩ :=
    CFSG.GroupTheory.exists_noncyclic_exponent_classTwo_normalized (G := Bar2 M) (p := q)
      hq2 hQp hnc
  refine ⟨Dbar, ?_, hQp.to_le hle, hne, hDnc, hexp, hcl⟩
  refine Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr ?_)
  calc (⊤ : Subgroup (Bar2 M))
      = Subgroup.normalizer (CFSG.pCore q (Bar2 M) : Set (Bar2 M)) :=
        (Subgroup.normalizer_eq_top_iff.mpr hQn).symm
    _ ≤ Subgroup.normalizer (Dbar : Set (Bar2 M)) := hnorm

theorem inf_centralizer_self_facts {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {Dbar : Subgroup H} (hDn : Dbar.Normal) (hDp : IsPGroup p ↥Dbar) (hDne : Dbar ≠ ⊥)
    (hDexp : ∀ y ∈ Dbar, y ^ p = 1) :
    (Dbar ⊓ Subgroup.centralizer (Dbar : Set H)).Normal ∧
      IsPGroup p ↥(Dbar ⊓ Subgroup.centralizer (Dbar : Set H)) ∧
      Dbar ⊓ Subgroup.centralizer (Dbar : Set H) ≠ ⊥ ∧
      CFSG.Open.IsElemAbelian p (Dbar ⊓ Subgroup.centralizer (Dbar : Set H)) := by
  haveI hDn' : Dbar.Normal := hDn
  haveI hCn : (Subgroup.centralizer (Dbar : Set H)).Normal := Subgroup.normal_centralizer
  refine ⟨Subgroup.normal_inf_normal _ _, hDp.to_le inf_le_left, ?_, ?_⟩
  · obtain ⟨z, hzD, hzo, hz⟩ :=
      CFSG.GroupTheory.WielandtProduct.exists_orderOf_eq_commute_of_isPGroup hDp hDne
    intro hbot
    have hzE : z ∈ Dbar ⊓ Subgroup.centralizer (Dbar : Set H) :=
      ⟨hzD, Subgroup.mem_centralizer_iff.mpr fun y hy => (hz y hy).eq.symm⟩
    rw [hbot, Subgroup.mem_bot] at hzE
    exact (Fact.out : p.Prime).ne_one (by rw [← hzo, hzE, orderOf_one])
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => hDexp y hy.1⟩
    change (a : H) * b = b * a
    exact Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1

theorem card_modEq_one_of_inf_centralizer_singleton_eq_bot {H : Type*} [Group H] [Finite H]
    {E : Subgroup H} (hEn : E.Normal) {x : H} {r : ℕ} (hr : r.Prime) (hxr : x ^ r = 1)
    (hfix : E ⊓ Subgroup.centralizer ({x} : Set H) = ⊥) :
    Nat.card E ≡ 1 [MOD r] := by
  haveI : Fact r.Prime := ⟨hr⟩
  refine CFSG.GroupTheory.card_modEq_one_of_isPGroup_normalizes_of_inf_centralizer_eq_bot
    (X := Subgroup.zpowers x) (IsPGroup.of_card_dvd_pow (n := 1) ?_) ?_ ?_
  · rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hxr
  · rw [Subgroup.normalizer_eq_top_iff.mpr hEn]
    exact le_top
  · rw [eq_bot_iff, ← hfix]
    exact fun y hy => ⟨hy.1, Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers x)) hy.2⟩

private theorem le_three_of_isElemAbelian_three_bar2 {M : Subgroup G}
    (hrk3 : CFSG.Open.pRank 3 M ≤ 3) {E : Subgroup (Bar2 M)}
    (hE : CFSG.Open.IsElemAbelian 3 E) {d : ℕ} (hd : Nat.card E = 3 ^ d) : d ≤ 3 := by
  have h1 : d ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 M)) :=
    CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_top hE hd
  rw [CFSG.Quasithin.pRank_modO2_eq M Nat.prime_three (by norm_num)] at h1
  exact h1.trans hrk3

theorem Ctx23L.false_of_mem_B0_not_mem_centralizer_Z {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h1930 : H1930 D) (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch)
    (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty) (hrk3 : CFSG.Open.pRank 3 D.M ≤ 3)
    (hnc : ¬ IsCyclic ↥(CFSG.pCore 3 (Bar2 D.M))) {b : G} (hb : b ∈ c.B0)
    (hbZ : b ∉ Subgroup.centralizer (D.Z : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr13 : r ≠ 13) (hbo : orderOf b = r) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbM : b ∈ D.M := c.hBM hb
  obtain ⟨Dbar, hDn, hDq, hDne, hDnc, hDexp, hDcl⟩ :=
    exists_bar2_normal_noncyclic_exponent_classTwo (M := D.M) Nat.prime_three (by norm_num) hnc
  have hfix := Ctx23L.centralizer_bar_inf_eq_bot c.withB0 h1930 h54 h6 h71 hsig
    (b := ⟨b, hbM⟩) (by simpa using hb) hbZ Nat.prime_three (by norm_num)
    hDn hDq hDnc hDexp hDcl
  obtain ⟨hEn, hEp, hEne, hEab⟩ := inf_centralizer_self_facts hDn hDq hDne hDexp
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hEp
  have hd3 : d ≤ 3 := le_three_of_isElemAbelian_three_bar2 hrk3 hEab hd
  have hd1 : 1 ≤ d := Nat.pos_of_ne_zero fun h0 =>
    hEne (Subgroup.card_eq_one.mp (by rw [hd, h0, pow_zero]))
  have hpow : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩ ^ r = 1 := by
    have h1 : (⟨b, hbM⟩ : ↥D.M) ^ r = 1 := by
      rw [← hbo, ← Subgroup.orderOf_mk b hbM]; exact pow_orderOf_eq_one _
    rw [← map_pow, h1, map_one]
  have hfix' : (Dbar ⊓ Subgroup.centralizer (Dbar : Set (Bar2 D.M))) ⊓
      Subgroup.centralizer ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩} :
        Set (Bar2 D.M)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    calc (Dbar ⊓ Subgroup.centralizer (Dbar : Set (Bar2 D.M))) ⊓
          Subgroup.centralizer ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩} :
            Set (Bar2 D.M))
        ≤ Dbar ⊓ Subgroup.centralizer
            ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, hbM⟩} : Set (Bar2 D.M)) :=
          inf_le_inf_right _ inf_le_left
      _ = ⊥ := hfix
  have hmod := card_modEq_one_of_inf_centralizer_singleton_eq_bot hEn hr hpow hfix'
  rw [hd] at hmod
  exact false_of_three_pow_modEq_one hr hr2 hr13 hd1 hd3 hmod

theorem s23_26OmegaCore_of (D : Data G) (Ch : Choice2011 G) (h52 : S23_5_2Omega D Ch)
    (h53 : S23_5_3 D Ch) (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch) (h71 : S23_7_1 D Ch)
    (hsig : D.sig.Nonempty) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ D.sig → CFSG.Open.pRank r D.M ≤ 3) :
    S23_26OmegaCore D Ch := by
  intro h1930 c hOmega h3 hnc
  have hcn : c.n = 2 * CFSG.Open.pRank 2 D.Z := (h52 h1930 c hOmega).2
  have hn : 3 ≤ c.n := hn3 h1930 c.toCtx23.toCtx21
  obtain ⟨r, hr, hrdvd, hr13⟩ :=
    exists_prime_dvd_two_pow_sub_one_ne_thirteen (m := CFSG.Open.pRank 2 D.Z) (by omega)
  have hr2 : r ≠ 2 :=
    (CFSG.GroupTheory.SuzukiTwoGroup.odd_two_pow_sub_one (by omega)).ne_two_of_dvd_nat hrdvd
  obtain ⟨b, hb, hbo, hbZ⟩ := c.exists_mem_B0_not_mem_centralizer_Z_of_dvd h53 h1930
    (by omega) (Dvd.intro_left 2 hcn.symm) hr hrdvd
  exact c.false_of_mem_B0_not_mem_centralizer_Z h1930 h54 h6 h71 hsig
    (hrk 3 Nat.prime_three (by norm_num) h3) hnc hb hbZ hr hr2 hr13 hbo

theorem s23_26Omega_full_of (D : Data G) (Ch : Choice2011 G) (h52 : S23_5_2Omega D Ch)
    (h53 : S23_5_3 D Ch) (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch) (h71 : S23_7_1 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hsig : D.sig.Nonempty) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ D.sig → CFSG.Open.pRank r D.M ≤ 3) :
    S23_26Omega D Ch :=
  s23_26Omega_of D Ch h52 h53 h54 h6 h71 hsp hsig hn3 hrk
    (s23_26OmegaCore_of D Ch h52 h53 h54 h6 h71 hsig hn3 hrk)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

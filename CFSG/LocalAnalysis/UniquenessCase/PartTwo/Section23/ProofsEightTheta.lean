module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightLift
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2115N

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

abbrev xbar (K : Subgroup G) : Type :=
  BarInf K ⧸ Subgroup.center (BarInf K)

noncomputable abbrev sylowImage (D : Data G) (K : Subgroup G) : Subgroup (xbar K) :=
  ((D.T ⊓ K).subgroupOf K).map (piBarInf K)

theorem center_eq_bot_of_isL2_or_isSz {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) {a : ℕ}
    (h : IsL2 (Bar2 K) a ∨ IsSz (Bar2 K) a) :
    Subgroup.center (Bar2 K) = ⊥ :=
  h.elim (center_eq_bot_of_isL2 hq) (center_eq_bot_of_isSz hq)

theorem exists_sylow_normalized {D : Data G} {Ch : Choice2011 G}
    (hBor : KBor) (h215 : S21_5 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) {a : ℕ}
    (hshape : IsL2 (Bar2 K) a ∨ IsSz (Bar2 K) a) {b : G} (hb : b ∈ c.B0)
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) :
    ∃ S : Sylow 2 (xbar K), (S : Subgroup (xbar K)) = sylowImage D K ∧
      ∀ x ∈ (S : Subgroup (xbar K)),
        inducedQuotInfAut K b hbN x ∈ (S : Subgroup (xbar K)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  have hc : Subgroup.center (Bar2 K) = ⊥ := center_eq_bot_of_isL2_or_isSz hq hshape
  have hLx : IsL2 (xbar K) a ∨ IsSz (xbar K) a :=
    hshape.elim (fun h => Or.inl (lieModel_xbar_of_lieModel_bar2 hq hc h))
      (fun h => Or.inr (lieModel_xbar_of_lieModel_bar2 hq hc h))
  have hZ : Subgroup.center (xbar K) = ⊥ := by
    obtain ⟨e⟩ := uc22p21k_quotCenter_equiv (center_barInf_eq_bot hq)
    exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e (center_barInf_eq_bot hq)
  have hP3 := Ctx23L.inducedQuotInfAut_mem_sylow (D := D) (Ch := Ch) hBor h215 h1930
    c hK hZ ⟨a, hLx.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))⟩ hb hbN
  obtain ⟨-, hSKp, hSKidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp
    (isSylowOf_map_piBarInf (D := D) (K := K) hK)
  let S : Sylow 2 (xbar K) := hSKp.toSylow (by simpa using hSKidx)
  have hScoe : (S : Subgroup (xbar K)) = sylowImage D K := IsPGroup.toSylow_coe hSKp _
  refine ⟨S, hScoe, ?_⟩
  intro x hx
  rw [hScoe] at hx ⊢
  exact hP3 x hx

theorem exists_thetaData {D : Data G} {Ch : Choice2011 G}
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch)
    (h53 : S23_5_3 D Ch) (h54 : S23_5_4 D Ch) (h215 : S21_5 D Ch)
    (hBor : KBor) (h1930 : H1930 D) (c : Ctx23L D Ch) {K : Subgroup G}
    (hK : K ∈ calC D.M) {a : ℕ} (hshape : IsL2 (Bar2 K) a ∨ IsSz (Bar2 K) a)
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ 2 ^ CFSG.Open.pRank 2 D.Z - 1) :
    ∃ (b : G) (hb : b ∈ c.B0) (hbN : b ∈ Subgroup.normalizer (K : Set G)),
      Odd (orderOf b) ∧ b ∉ Subgroup.centralizer (D.Z : Set G) ∧
      Odd (orderOf (inducedQuotInfAut K b hbN)) ∧
      ∃ (S : Sylow 2 (xbar K)),
        (S : Subgroup (xbar K)) = sylowImage D K ∧
        (∀ x ∈ (S : Subgroup (xbar K)),
          inducedQuotInfAut K b hbN x ∈ (S : Subgroup (xbar K))) ∧
        (∀ p : ℕ, p.Prime → ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup p ↥X →
          X ≤ D.M ⊓ Subgroup.centralizer ({b} : Set G) → X ∉ uniqueSet D.M) := by
  classical
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  obtain ⟨hm2, hP1⟩ := c.exists_mem_B0_not_mem_centralizer_Z hE h207 h52 h53 h1930
  obtain ⟨b, hb0, hborder, hbZ⟩ := hP1 r hr hrdvd
  have hoddpow : Odd (2 ^ CFSG.Open.pRank 2 D.Z - 1) :=
    CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
  have hr2 : r ≠ 2 := by
    intro h2
    exact hoddpow.not_two_dvd_nat (h2 ▸ hrdvd)
  have hbodd : Odd (orderOf b) := hborder ▸ hr.odd_of_ne_two hr2
  have hbN : b ∈ Subgroup.normalizer (K : Set G) :=
    c.B0_le_normalizer_of_mem_calC h215 h1930 hK hb0
  have hθodd : Odd (orderOf (inducedQuotInfAut K b hbN)) :=
    Odd.of_dvd_nat hbodd (orderOf_inducedQuotInfAut_dvd K hbN)
  obtain ⟨S, hScoe, hSinv⟩ :=
    exists_sylow_normalized hBor h215 h1930 c hK hshape hb0 hbN
  refine ⟨b, hb0, hbN, hbodd, hbZ, hθodd, S, hScoe, hSinv, ?_⟩
  intro p hp X hXne hXp hXle
  exact ((h54 h1930 c.withB0 b (by simpa using hb0) hbZ).2 p hp X hXne hXp hXle).1

theorem exists_prime_order_centralizer_of_caseB {D : Data G} {K : Subgroup G} {b : G}
    {a : ℕ} (hK : K ∈ calC D.M) (hshape : IsL2 (Bar2 K) a ∨ IsSz (Bar2 K) a)
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hbodd : Odd (orderOf b))
    {s : ℕ} (hsdvd : s ∣ a) (hsodd : Odd s) (hsne : s ≠ 1)
    {x : xbar K} (hxord : orderOf x = 2 ^ s - 1)
    (hxfix : inducedQuotInfAut K b hbN x = x) :
    ∃ (r : ℕ) (y : ↥K), r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ s - 1 ∧
      (y : G) ∈ Subgroup.centralizer ({b} : Set G) ∧ orderOf (y : G) = r := by
  classical
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  have hc : Subgroup.center (Bar2 K) = ⊥ := center_eq_bot_of_isL2_or_isSz hq hshape
  have hs3 : 3 ≤ s := by
    rcases hsodd with ⟨k, hk⟩
    omega
  have hne : 2 ^ s - 1 ≠ 1 := by
    have h2 : 2 ^ 3 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs3
    norm_num at h2
    omega
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne
  have hr2 : r ≠ 2 := by
    intro h2
    have hpowodd : Odd (2 ^ s - 1) := CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
    exact hpowodd.not_two_dvd_nat (h2 ▸ hrdvd)
  have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hxr : orderOf (x ^ ((2 ^ s - 1) / r)) = r := by
    have h := orderOf_pow_orderOf_div (x := x) hx0 (n := r) (by rw [hxord]; exact hrdvd)
    simpa [hxord] using h
  have hxrfix : inducedQuotInfAut K b hbN (x ^ ((2 ^ s - 1) / r)) =
      x ^ ((2 ^ s - 1) / r) := by
    rw [map_pow, hxfix]
  have hrZ : ¬ r ∣ Nat.card (Subgroup.center (Bar2 K)) := by
    rw [hc, Subgroup.card_bot, Nat.dvd_one]
    exact hr.ne_one
  obtain ⟨y, hyC, hyord, -⟩ :=
    exists_mem_centralizer_of_quotInf_fixed hK hbN hbodd hr hr2 hrZ hxr hxrfix
  exact ⟨r, y, hr, hr2, hrdvd, hyC, hyord⟩

theorem normal_of_caseB {D : Data G} {Ch : Choice2011 G}
    (h2115 : S21_15N D Ch) (h54 : S23_5_4 D Ch) (hsig : D.sig.Nonempty) (h1930 : H1930 D)
    (c : Ctx23L D Ch) {K : Subgroup G} (hK : K ∈ calC D.M) {a : ℕ}
    (hshape : IsL2 (Bar2 K) a ∨ IsSz (Bar2 K) a)
    {b : G} (hb : b ∈ c.B0) (hbN : b ∈ Subgroup.normalizer (K : Set G))
    (hbodd : Odd (orderOf b)) (hbZ : b ∉ Subgroup.centralizer (D.Z : Set G))
    {s : ℕ} (hsdvd : s ∣ a) (hsodd : Odd s) (hsne : s ≠ 1)
    {x : xbar K} (hxord : orderOf x = 2 ^ s - 1)
    (hxfix : inducedQuotInfAut K b hbN x = x) : (K.subgroupOf D.M).Normal := by
  classical
  obtain ⟨r, y, hr, -, hrdvd, hyC, hyord⟩ :=
    exists_prime_order_centralizer_of_caseB hK hshape hbN hbodd hsdvd hsodd hsne hxord hxfix
  let A : Subgroup G := Subgroup.zpowers (y : G)
  have hAcard : Nat.card A = r := by
    change Nat.card (Subgroup.zpowers (y : G)) = r
    rw [Nat.card_zpowers, hyord]
  have hAK : A ≤ K := Subgroup.zpowers_le.mpr y.2
  have hAM : A ≤ D.M := hAK.trans hK.1.le
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := Subgroup.zpowers_le.mpr hyC
  by_cases hconj : conjClosure D.M K = K
  · exact uc22p21j_normal_of_conjClosure_eq hK.1.le hconj.symm
  · exfalso
    obtain ⟨p, hp⟩ := hsig
    have huniq := (h2115 h1930 c.withB0.toCtx23.toCtx21 K hK a hshape hconj s hsodd
      hsdvd r hr hrdvd p hp A hAcard hAK).1.2
    have hAne : A ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hAcard
      exact hr.ne_one hAcard.symm
    haveI : Fact (Nat.Prime r) := ⟨hr⟩
    have hpgrp : IsPGroup r ↥A := IsPGroup.iff_card.mpr ⟨1, by simpa using hAcard⟩
    exact ((h54 h1930 c.withB0 b (by simpa using hb) hbZ).2 r hr A hAne hpgrp
      (le_inf hAM hAC)).1 huniq

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

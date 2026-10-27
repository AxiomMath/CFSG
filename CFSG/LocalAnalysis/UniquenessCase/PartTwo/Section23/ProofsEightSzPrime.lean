module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightTheta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightSz
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214g
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.GroupTheory.SteinbergCBHHBNumberTheory

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem sz_field_part {D : Data G} {Ch : Choice2011 G}
    (hBor : KBor) (h215 : S21_5 D Ch) (h54 : S23_5_4 D Ch) (h2115 : S21_15N D Ch)
    (hsig : D.sig.Nonempty) (h1930 : H1930 D) (c : Ctx23L D Ch) {K : Subgroup G}
    (hK : K ∈ calC D.M) {a : ℕ} (hSz : IsSz (Bar2 K) a)
    (hne : conjClosure D.M K ≠ K) (hCentSz : KCentSz) {b : G} (hb0 : b ∈ c.B0)
    (hbN : b ∈ Subgroup.normalizer (K : Set G))
    (hbZ : b ∉ Subgroup.centralizer (D.Z : Set G)) :
    a ∣ orderOf (inducedQuotInfAut K b hbN) ∧
      (∀ x ∈ Subgroup.normalizer ((sylowImage D K : Set (xbar K))),
        inducedQuotInfAut K b hbN x * x⁻¹ ∈ sylowImage D K → x ∈ sylowImage D K) := by
  classical
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  have hc : Subgroup.center (Bar2 K) = ⊥ := center_eq_bot_of_isSz hq hSz
  have hSzh : IsSz (xbar K) a := lieModel_xbar_of_lieModel_bar2 hq hc hSz
  obtain ⟨S, hScoe, hSinv⟩ :=
    exists_sylow_normalized hBor h215 h1930 c hK (Or.inr hSz) hb0 hbN
  have hbodd : Odd (orderOf b) := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 hb0
  have hθodd : Odd (orderOf (inducedQuotInfAut K b hbN)) :=
    Odd.of_dvd_nat hbodd (orderOf_inducedQuotInfAut_dvd K hbN)
  obtain ⟨s, hsdvd, hdiv, ⟨x, hxord, hxfix⟩, hfp⟩ :=
    hCentSz (xbar K) a hSzh (inducedQuotInfAut K b hbN) hθodd S hSinv
  have hodd_a : Odd a := CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hSz
  have hs1 : s = 1 := by
    by_contra hsne
    have hsodd : Odd s := Odd.of_dvd_nat hodd_a hsdvd
    have hnorm : (K.subgroupOf D.M).Normal :=
      normal_of_caseB h2115 h54 hsig h1930 c hK (Or.inr hSz) hb0 hbN hbodd hbZ
        hsdvd hsodd hsne hxord hxfix
    exact hne (uc22p2214_conjClosure_eq_of_normal hK.1.le hnorm)
  refine ⟨?_, ?_⟩
  · simpa [hs1] using hdiv
  · intro x hxN hxmod
    have hxS := hfp hs1 x (by rwa [← hScoe] at hxN) (by rwa [← hScoe] at hxmod)
    rwa [hScoe] at hxS

private theorem sz_mersenne_eq {m a : ℕ} (hm2 : 2 ≤ m)
    (h_all : ∀ r : ℕ, r.Prime → r ∣ 2 ^ m - 1 → r = a) :
    a = 2 ^ m - 1 ∧ a.Prime := by
  classical
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hne1 : 2 ^ m - 1 ≠ 1 := by omega
  obtain ⟨r0, hr0, hr0dvd⟩ := Nat.exists_prime_and_dvd hne1
  have ha_prime : a.Prime := by
    simpa [h_all r0 hr0 hr0dvd] using hr0
  have hne0 : 2 ^ m - 1 ≠ 0 := by omega
  have hpow : 2 ^ m - 1 = a ^ (2 ^ m - 1).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hne0 (fun {d} hd hdvd => h_all d hd hdvd)
  have hkpos : 1 ≤ (2 ^ m - 1).primeFactorsList.length := by
    by_contra hk
    have hk0 : (2 ^ m - 1).primeFactorsList.length = 0 := by omega
    rw [hk0, pow_zero] at hpow
    omega
  have hk1 : (2 ^ m - 1).primeFactorsList.length = 1 :=
    (CFSG.GroupTheory.HallHigmanB.two_pow_sub_one_eq_prime_pow ha_prime hkpos hpow).1
  refine ⟨?_, ha_prime⟩
  have h : 2 ^ m - 1 = a := by simpa [hk1] using hpow
  exact h.symm

theorem Ctx23L.szPrime_of_ne {D : Data G} {Ch : Choice2011 G}
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch)
    (h54 : S23_5_4 D Ch) (h215 : S21_5 D Ch) (h2115 : S21_15N D Ch) (hBor : KBor)
    (hCentSz : KCentSz) (hsig : D.sig.Nonempty) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) {a : ℕ} (hSz : IsSz (Bar2 K) a)
    (hne : conjClosure D.M K ≠ K) :
    a = 2 ^ CFSG.Open.pRank 2 D.Z - 1 ∧ a.Prime ∧
      ∀ b ∈ c.B0, ∀ hbN : b ∈ Subgroup.normalizer (K : Set G),
        b ∉ Subgroup.centralizer (D.Z : Set G) →
          ∀ x ∈ Subgroup.normalizer ((sylowImage D K : Set (xbar K))),
            inducedQuotInfAut K b hbN x * x⁻¹ ∈ sylowImage D K → x ∈ sylowImage D K := by
  classical
  have hm2 : 2 ≤ CFSG.Open.pRank 2 D.Z :=
    (c.exists_mem_B0_not_mem_centralizer_Z hE h207 h52 h53 h1930).1
  have hP1 : ∀ r : ℕ, r.Prime → r ∣ 2 ^ CFSG.Open.pRank 2 D.Z - 1 →
      ∃ b ∈ c.B0, orderOf b = r ∧ b ∉ Subgroup.centralizer (D.Z : Set G) :=
    (c.exists_mem_B0_not_mem_centralizer_Z hE h207 h52 h53 h1930).2
  have hodd_a : Odd a := CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hSz
  have h3a : 3 ≤ a := CFSG.LocalAnalysis.EvenBN.GMSK.three_le_of_lieModel_twistedB2 hSz
  have h_all : ∀ r : ℕ, r.Prime → r ∣ 2 ^ CFSG.Open.pRank 2 D.Z - 1 → r = a := by
    intro r hr hrdvd
    obtain ⟨b, hb0, hborder, hbZ⟩ := hP1 r hr hrdvd
    have hbN : b ∈ Subgroup.normalizer (K : Set G) :=
      c.B0_le_normalizer_of_mem_calC h215 h1930 hK hb0
    have hdvdθ : a ∣ orderOf (inducedQuotInfAut K b hbN) :=
      (sz_field_part hBor h215 h54 h2115 hsig h1930 c hK hSz hne hCentSz hb0 hbN hbZ).1
    have hdvd : a ∣ r := by
      have h := hdvdθ.trans (orderOf_inducedQuotInfAut_dvd K hbN)
      simpa [hborder] using h
    rcases (Nat.dvd_prime hr).mp hdvd with h1 | h1
    · omega
    · exact h1.symm
  obtain ⟨ha_eq, ha_prime⟩ := sz_mersenne_eq hm2 h_all
  refine ⟨ha_eq, ha_prime, ?_⟩
  intro b hb0 hbN hbZ x hxN hxmod
  exact (sz_field_part hBor h215 h54 h2115 hsig h1930 c hK hSz hne hCentSz hb0 hbN hbZ).2
    x hxN hxmod

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

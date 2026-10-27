module

public import CFSG.RankThree.PartOne.N143.SectionReduce
public import CFSG.RankThree.PartOne.N143X.EvenRankTwo
public import CFSG.RankThree.PartOne.N143X.EvenOrth
public import CFSG.RankThree.PartOne.N143X.EvenSpin
public import CFSG.RankThree.PartOne.N143X.EvenChev
public import CFSG.RankThree.PartOne.N143X.EvenExtra
public import CFSG.RankThree.PartOne.N143X.G2Rank

public section

namespace CFSG.RankThree.PartOne.N143X

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.N143

theorem kf64wSimple_holds
    (hEx : EvenRankTwoExceptionalNoPCube) : KF64WSimple := by
  intro X _ _ hs hnonab hK he hEven p hp hp7 E hE hcard
  show (Nat.card E.normalizerMonoidHom.range).factorization 3 ≤ 1
  obtain ⟨t, n, f, hadm, hLie⟩ := hEven
  rcases hLie with ⟨ht, hmod⟩ | ⟨hn0, ht, hmod⟩ | ⟨hn0, ht, hmod⟩ | ⟨hn0, rfl, hmod⟩
  ·
    cases t
    case PSL =>
      by_cases h5 : n ≤ 5
      · exact factorization_three_psl_le h5 hmod hp hp7 hE
      · exfalso
        have hf : 1 ≤ f := hmod.1.2.1
        by_cases hbig : (6 ≤ n ∧ 2 ≤ f) ∨ 8 ≤ n
        · exact false_of_psl_large hmod hbig he
        · have hf1 : f = 1 := by omega
          have hn67 : n = 6 ∨ n = 7 := by omega
          subst hf1
          exact false_of_pow_three_psl_two hn67 hmod hp hp7 hcard
    case PSU =>
      by_cases h5 : n ≤ 5
      · exact factorization_three_psu_le h5 hmod hp hp7 hE
      · exfalso
        have hf : 1 ≤ f := hmod.1.2.1
        by_cases hbig : 7 ≤ n ∨ (n = 6 ∧ 2 ≤ f)
        · exact false_of_psu_large hmod hbig he
        · have hn6 : n = 6 := by omega
          have hf1 : f = 1 := by omega
          subst hn6
          subst hf1
          exact false_of_pow_three_psu_six_two hmod hp hp7 hcard
    case PSp =>
      by_cases h4 : n ≤ 4
      · exact factorization_three_psp_le h4 hmod hp hp7 hE
      · exact (false_of_psp_large hmod (by omega) he).elim
    case POmegaOdd => exact absurd rfl hmod.1.2.2.2
    case POmegaPlus =>
      by_cases h4 : n ≤ 4
      · exact factorization_three_pomegaPlus_le h4 hmod hp hp7 hE
      · exact (false_of_pomegaPlus_large hmod (by omega) he).elim
    case POmegaMinus =>
      by_cases h4 : n ≤ 4
      · exact factorization_three_pomegaMinus_le h4 hmod hp hp7 hE
      · exact (false_of_pomegaMinus_large hmod (by omega) he).elim
    all_goals exact hmod.2.elim
  ·
    cases t
    case G2 =>
      exfalso
      obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hmod
      have hC : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
      let e : X ≃* adjointGroup .G2 K :=
        e₀.trans ((QuotientGroup.quotientMulEquivOfEq hC).trans QuotientGroup.quotientBot)
      have hpq : ¬ p ∣ Nat.card K := by
        rw [hK]
        intro h
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
        omega
      refine false_of_pow_three_G2 K hp hp7 hpq (E := E.map (e : X →* adjointGroup .G2 K)) ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        change (e x) ^ p = 1
        rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian x hx, map_one]
      · rw [← Nat.card_congr (e.subgroupMap E).toEquiv]
        exact hcard
    case trialityD4 => exact absurd hcard (hEx X f (Or.inl hmod) p hp hp7 E hE)
    case F4 =>
      by_cases hf2 : 2 ≤ f
      · exact (false_of_chevalley_exc (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hf2⟩)))) hmod
          he).elim
      · have hf1 : f = 1 := by
          have := hmod.1.2.1
          omega
        subst hf1
        exact (false_of_pow_three_F4_two (by simpa using hmod.2) hp hp7 hcard).elim
    case E6 => exact (false_of_chevalley_exc (Or.inl rfl) hmod he).elim
    case E7 => exact (false_of_chevalley_exc (Or.inr (Or.inl rfl)) hmod he).elim
    case E8 => exact (false_of_chevalley_exc (Or.inr (Or.inr (Or.inl rfl))) hmod he).elim
    case twistedE6 =>
      exact (false_of_chevalley_exc (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hmod he).elim
    all_goals exact absurd ht (by decide)
  ·
    cases t
    case twistedG2 => exact absurd hmod.1.2.2.2.1 (by norm_num)
    case twistedF4 => exact absurd hcard (hEx X f (Or.inr hmod) p hp hp7 E hE)
    case Tits => exact (false_of_pow_three_tits hmod hp hp7 hcard).elim
    all_goals exact absurd ht (by decide)
  ·
    exact factorization_three_suzuki hmod hp hp7 hE

end CFSG.RankThree.PartOne.N143X

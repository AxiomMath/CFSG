module

public import CFSG.RankThree.PartOne.KF.F128Cls
public import CFSG.RankThree.PartOne.KF.F122PSL
public import CFSG.RankThree.PartOne.KF.ClsPSLBig
public import CFSG.RankThree.PartOne.KF.ClsPSLSmall
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.RankThree.PartOne.KF.F128Syl
public import CFSG.RankThree.PartOne.S11d.PSLRank

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.KFU
open CFSG.RankThree.PartOne.K1214 (SylowShape)
open Matrix

theorem pRank_statedProj_statedSL_le {K : Type} [Field K] [Finite K] {n p k : ℕ} (hp : p.Prime)
    (hpn : ¬ p ∣ n)
    (hbound : ∀ E : Subgroup (GL (Fin n) K), E ≤ StatedSL n K →
      (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) → (∀ g ∈ E, g ^ p = 1) → Nat.card E ≤ p ^ k) :
    CFSG.pRank p (StatedProj (StatedSL n K)) ≤ k := by
  have hq := isCentralPQuot_statedSL_of_not_dvd (K := K) hp hpn
  have hcop : ¬ p ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) := by
    have := hq.coprime
    rw [QuotientGroup.ker_mk'] at this
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp this
  rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp _ hcop,
    CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.RankThree.PartOne.LIT.pRank_le_of_card_gl hp.one_lt (StatedSL n K) hbound

theorem kf128SylTag_PSL
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF128SylTag .PSL := by
  intro J _ _ hq he T _ _ π hπ hker p hp hp5 hkerp hLR2 n f₀ hf₀ hM α hαp hαinn hLRA hX hF hrk
  classical
  exfalso
  have hp2 : p ≠ 2 := by omega
  have hf5 : 5 ≤ p * f₀ := by nlinarith
  have hf1 : 1 ≤ p * f₀ := by omega
  have hcl : StatedClassicalModel T .PSL n 2 (p * f₀) :=
    K1214.statedClassicalModel_of_lieModel_of_tag' (Or.inr (Or.inr rfl)) hM
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := id hcl
  have hn2 : 2 ≤ n := hadm.2.2.1
  have : CharP K 2 := K128.charP_two_of_card_eq_two_pow hK
  have hT0 : Subgroup.center T = ⊥ := center_eq_bot_of_cover hq.1 π hπ hcl
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have h1 := (CharP.cast_eq_zero_iff K 2 p).mp h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h1).symm
  have hlr : ∀ r : ℕ, r.Prime → localRank r T = localRank r (StatedProj (StatedSL n K)) :=
    fun r hr => CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hr
  have hrank : ∀ k, (¬ p ∣ n) →
      (∀ E : Subgroup (GL (Fin n) K), E ≤ StatedSL n K →
        (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) → (∀ g ∈ E, g ^ p = 1) → Nat.card E ≤ p ^ k) →
      CFSG.pRank p T ≤ k := by
    intro k hpn hb
    rw [pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e]
    exact pRank_statedProj_statedSL_le hp hpn hb
  by_cases hn5 : 5 ≤ n
  ·
    set e' : T ≃* ProjectiveSpecialLinearGroup (Fin n) K :=
      e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm with he'
    set π' : J →* ProjectiveSpecialLinearGroup (Fin n) K := (e' : T →* _).comp π with hπ'
    have hπ's : Function.Surjective π' := e'.surjective.comp hπ
    have hπ'c : π'.ker ≤ Subgroup.center J := by
      intro x hx
      apply hker
      rw [MonoidHom.mem_ker] at hx ⊢
      exact (map_eq_one_iff e' e'.injective).1 hx
    obtain ⟨ρ, hρs, hρk⟩ := exists_cover_psl hGA hn5 hf1 hK hq.1 π' hπ's hπ'c
    obtain ⟨r, hr, hr2, hr5, hrd⟩ :=
      exists_odd_prime_dvd_two_pow_sub_one_ne_five (f := p * f₀) (by omega)
    have hrK : r ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; exact hrd
    have hcen : 4 + 1 < n ∨ ¬ r ∣ n := by
      by_cases hn6 : 6 ≤ n
      · exact Or.inl (by omega)
      · right
        have : n = 5 := by omega
        subst this
        intro hrn
        exact hr5 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp hrn)
    have h4 := le_localRank_of_surjective_torus hr hrK (by omega : 4 < n) (by omega) hcen ρ hρs hρk
    have h3 := (CFSG.RankThree.OddKernel.localRank_le_evenRank hr hr2).trans he
    omega
  · have hpn : ¬ p ∣ n := fun hd => by
      have := Nat.le_of_dvd (by omega) hd
      omega
    have hn : n = 2 ∨ n = 3 ∨ n = 4 := by omega
    have hq1 : ¬ p ∣ 2 ^ (p * f₀) - 1 → ¬ p ∣ Nat.card K ^ 1 - 1 := by
      intro hdvd
      rwa [hK, pow_one]
    rcases hn with rfl | rfl | rfl
    ·
      have := hrank 1 hpn (by
        intro E hE hcomm hexp
        have := LIT.card_le_of_det_eq_one_gl_two hp hpK (by simp) E hcomm hexp
          (fun g hg => mem_statedSL_iff.mp (hE hg))
        simpa using this)
      omega
    ·
      by_cases hdvd : p ∣ 2 ^ (p * f₀) - 1
      · exact false_of_row kf122Row1_holds hp hp5 hT0
          ⟨p * f₀, hf1, hdvd, statedClassicalModel_congr (topQuotEquiv hT0) hcl⟩ hLR2 hαp hαinn hLRA
      · have := hrank 1 hpn (by
          intro E hE hcomm hexp
          have := LIT.card_le_pow_div_gl hp hpK (d := 2) (by norm_num) (by
            intro i hi0 hi2
            have hi1 : i = 1 := by omega
            subst hi1
            exact hq1 hdvd) E hcomm hexp
          simpa using this)
        omega
    ·
      by_cases hm : p ∣ 2 ^ (p * f₀) - 1
      · have hrK : p ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; exact hm
        have h3 := CFSG.RankThree.PartTwo.Census.le_localRank_PSL_torus (K := K) (m := 3) (n := 4)
          hp hrK (by norm_num) (by norm_num) (Or.inr (fun hd => by
            have := Nat.le_of_dvd (by norm_num) hd
            omega))
        rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
          (projectiveSpecialLinearGroupEquivStatedProj 4 K) hp, ← hlr p hp] at h3
        exact false_of_three_le_localRank hp hLR2 h3
      · by_cases hm1 : p ∣ 2 ^ (p * f₀) + 1
        · exact false_of_row kf122Row8_holds hp hp5 hT0
            ⟨p * f₀, hf1, hm1, statedClassicalModel_congr (topQuotEquiv hT0) hcl⟩ hLR2 hαp hαinn
            hLRA
        · have hsq : ¬ p ∣ Nat.card K ^ 2 - 1 := by
            intro hd
            have h2f : 2 ≤ 2 ^ (p * f₀) := by
              calc 2 = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) hf1
            have hfac : (2 ^ (p * f₀)) ^ 2 - 1 = (2 ^ (p * f₀) - 1) * (2 ^ (p * f₀) + 1) := by
              have : 1 ≤ 2 ^ (p * f₀) := Nat.one_le_two_pow
              zify [this, Nat.one_le_pow 2 (2 ^ (p * f₀)) (by omega)]
              ring
            rw [hK, hfac] at hd
            rcases hp.dvd_mul.mp hd with h1 | h1
            · exact hm h1
            · exact hm1 h1
          have := hrank 1 hpn (by
            intro E hE hcomm hexp
            have := LIT.card_le_pow_div_gl hp hpK (d := 3) (by norm_num) (by
              intro i hi0 hi3
              have hi : i = 1 ∨ i = 2 := by omega
              rcases hi with rfl | rfl
              · exact hq1 hm
              · exact hsq) E hcomm hexp
            simpa using this)
          omega

end CFSG.RankThree.PartOne

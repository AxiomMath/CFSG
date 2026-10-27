module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213TDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22P218s
import CFSG.LocalAnalysis.UniquenessCase.UC22S217Sp4
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229CongD
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.Quasithin.EmptyFaithful.R3c18W
import CFSG.Quasithin.Vol2.Ch1Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

theorem uc22s218p_pRank_le_one_sp4 {X : Type} [Group X] [Finite X] {n p : ℕ} (hX : IsSp4 X n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ (2 ^ n) ^ 2 - 1) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hZ : ¬ p ∣ Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)) := by
    intro h
    have h1 := CFSG.LieType.Steinberg.card_statedScalars_subgroupOf_statedSp_le_two 2 K
    have h2 := Nat.le_of_dvd Nat.card_pos h
    have h3 := hp.two_le
    omega
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e,
    CFSG.SectionRank.pRank_quotient_eq _ hZ, ← CFSG.SectionRank.pRank_eq_open_pRank_top]
  by_contra h
  exact hpd (hK ▸ CFSG.Quasithin.R3c18.dvd_sq_sub_one_of_two_le_pRank_sp4
    CFSG.Quasithin.R3c18.sp4PRankShape_holds hp hp2 hpK (by omega))

variable {G : Type} [Group G] [Finite G]

theorem uc22s218p_pRank_le_one_of_bar2 {L : Subgroup G} {n p : ℕ} (hX : IsSp4 (Bar2 L) n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ (2 ^ n) ^ 2 - 1) : CFSG.Open.pRank p L ≤ 1 := by
  rw [← CFSG.Quasithin.pRank_modO2_eq L hp hp2]
  exact uc22s218p_pRank_le_one_sp4 hX hp hp2 hpd

theorem uc22s218p_false_of_rank {D : Data G} {Ch : Choice2011 G} (h211 : S21_1 D Ch)
    (hH : H1930 D) (c : Ctx21 D Ch) (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D)
    (h76 : F07.R76Sig D) {L : Subgroup G} (hL : L ∈ calC D.M) [(L.subgroupOf D.M).Normal]
    {n : ℕ} (hn : Odd n) (hX : IsSp4 (Bar2 L) n) {p : ℕ} (hp : p ∈ D.sig)
    (hpn : ¬ p ∣ 2 ^ n - 1) (hrank : CFSG.Open.pRank p L + 2 ≤ CFSG.Open.pRank p D.M) :
    False := by
  have hns := UC6S846.not_solvable_of_mem_calC hL
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hsp := UC6S846.sp_of_mem_sig hSg hns hp
  have hLM : L ≤ D.M := hL.1.le
  have hML : D.M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  have hCL : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ n - 1 → ¬ IsStronglyPEmbedded r D.M :=
    fun r hr hr2 hrn => uc22p218s_not_stronglyEmbedded D Ch h211 hH c hLM hML hX hn hr hr2 hrn
  have hn3 : 3 ≤ n := uc22p218d_three_le_of_odd hX hn
  have h8 : 8 ≤ 2 ^ n :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd (by omega) hrn
  have hrσ : r ∉ D.sig := fun h => hCL r hr hr2 hrn (UC6S846.sp_of_mem_sig hSg hns h)
  obtain ⟨E, Q, hEL, hEel, hEc, hQM, hQel, hQc, hpow⟩ :=
    uc22p218s_exists_pow_torus hLM hX hpp hp2 hpn hr hr2 hrn hrank
  have hEM : E ≤ D.M := hEL.trans hLM
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    rw [card_bot] at hEc
    exact (Nat.one_lt_pow two_ne_zero hr.one_lt).ne hEc
  obtain ⟨x, hxQ, hx1, hxC⟩ := uc22p218s_exists_mem_centralizer hpp hr hQel hQc hEel hE1 hpow
  have hxle : zpowers x ≤ D.M ⊓ centralizer (E : Set G) := zpowers_le.2 ⟨hQM hxQ, hxC⟩
  have hpos : 1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (E : Set G)) :=
    UC6S846.le_pRank' hpp hxle (isElemAbelian_zpowers (hQel.2 x hxQ))
      (by rw [Nat.card_zpowers, orderOf_eq_prime (hQel.2 x hxQ) hx1, pow_one])
  have hXN : ∀ X : Subgroup G, X ≤ E → Nat.card X = r →
      1 < CFSG.Open.pRank p (D.M ⊓ normalizer (X : Set G)) := by
    intro X hXE _
    have hQX : Q ≤ normalizer (X : Set G) := le_normalizer_iff.2 fun y hy z hz => by
      obtain ⟨k, hk⟩ := hpow y hy
      rw [hk z (hXE hz)]
      exact pow_mem hz k
    have h2 := UC6S846.le_pRank' hpp (le_inf hQM hQX) hQel hQc
    omega
  obtain ⟨R, hR, hER⟩ := UC6.exists_isSylowOf_ge hEM hEel.isPGroup
  have hEC : E ≤ centralizer (R : Set G) :=
    uc22p218s_le_centralizer hX hr hr2 hrn hML hR hER hEL hEel.2
  have hΓ := h76 p hp hp2 hsp r hr E hEM hEel hEc hpos hXN
  exact hCL r hr hr2 hrn
    (h614 (UC6S846.sig_subset_sig1 hSg hns) r hr hr2 hrσ R hR E (le_inf hER hEC) hEel hEc hΓ)

theorem s21_8P_of_conclusion76 (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) : S21_8P D Ch := by
  intro _ hH c L hL n hn hX p hp
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  haveI : (L.subgroupOf D.M).Normal := s21_normalSp4_of D Ch hSg h211 hH c L hL n hn hX
  have hLM : L ≤ D.M := hL.1.le
  have hpn : ¬ p ∣ 2 ^ n - 1 := fun h =>
    uc22p218s_not_stronglyEmbedded D Ch h211 hH c hLM (le_normalizer_of_normal_subgroupOf hLM)
      hX hn hpp hp2 h (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hp)
  by_contra hcong
  have hpd : ¬ p ∣ (2 ^ n) ^ 2 - 1 := by
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 :=
      ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
    have e1 : (k + 1) ^ 2 - 1 = k * (k + 2) := Nat.sub_eq_of_eq_add (by ring)
    rw [hk, e1]
    intro h
    rcases (Nat.Prime.dvd_mul hpp).1 h with h | h
    · exact hpn (by rw [hk, Nat.add_sub_cancel]; exact h)
    · exact hcong (uc22ine229_modEq_of_dvd (by rw [hk]; exact h))
  have hrank : CFSG.Open.pRank p L + 2 ≤ CFSG.Open.pRank p D.M := by
    have h1 := uc22s218p_pRank_le_one_of_bar2 hX hpp hp2 hpd
    have h3 := hSg.three_le p hp
    omega
  exact uc22s218p_false_of_rank h211 hH c hSg h614 h76 hL hn hX hp hpn hrank

end CFSG.LocalAnalysis.UniquenessCase.UC22

module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront78Nar
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UsePair
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ud
import CFSG.LocalAnalysis.UniquenessCase.UCFront08UseS
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.UniquenessCase.UC22P22vd
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ue
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
import CFSG.Goldschmidt.StatementsG2
import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.G37Core
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case1
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3
import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
import CFSG.Quasithin.H13.QRCThreeFreeRankOneStep
import CFSG.Quasithin.SteinbergBKHigherElementaryThompson
import CFSG.RankThree.PartOne.Q1327T.Defs
import CFSG.RankThree.PartOne.Q1327T.ThetaLift
import CFSG.RankThree.PartTwo.KFacts.KS116Proof
import CFSG.RankThree.PartTwo.Sec11.Item1115
import CFSG.RankThree.PartTwo.Sec11.Item116H3Main
import CFSG.RankThree.PartTwo.Sec11.Item116R1CD
import CFSG.RankThree.PartTwo.Sec11.Item116R2NoHoles
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec11.Item119K
import CFSG.RankThree.PartTwo.Sec11.LSSolvableProof
import CFSG.RankThree.PartTwo.Sec11.Transitivity
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec4.Statements423
import CFSG.RankThree.PartTwo.Sec4.T444.Basic
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.Walter.Bender1970.S2
import CFSG.Walter.Bender1970.S3.Basic
import CFSG.Walter.Bender1970.S3.OStar
import CFSG.Walter.PSL2Facts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p2213a_n_ne_zero (D : Data G) {Ch : Choice2011 G} (c : Ctx21 D Ch) : c.n ≠ 0 := by
  intro h0
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (Nat.card c.B0 + 1)
  have hmem : p ∈ etaSet c.n := ⟨hp, by rw [h0]; simp⟩
  rw [← c.hpi] at hmem
  have hpos : 0 < Nat.card c.B0 := Nat.card_pos
  have := Nat.le_of_dvd hpos hmem.2
  omega

theorem uc22p2213a_centralizesBar_of_prime {L : Subgroup G} {n r : ℕ} (hL2 : IsL2 (Bar2 L) n)
    (hr : r.Prime) (hrn : ¬ r ∣ n) (hrL : ¬ r ∣ Nat.card (Bar2 L)) {a : G}
    (ha : a ∈ normalizer (L : Set G)) (har : a ^ r = 1) : CentralizesBar a L := by
  let m : ↥(normalizer (L : Set G)) := ⟨a, ha⟩
  have hmr : m ^ r = 1 := Subtype.ext (by simp [m, har])
  have hα : UC6S846.rhoL L m ^ r = 1 := by rw [← map_pow, hmr, map_one]
  obtain ⟨x, hx⟩ := uc22p2214_inner_of_prime_L2 hL2 hr hrn hα
  have hN : UC6S846.rhoL L m ^ Nat.card (Bar2 L) = 1 := by
    rw [← hx, ← map_pow, pow_card_eq_one', map_one]
  have h1 : orderOf (UC6S846.rhoL L m) ∣ Nat.gcd r (Nat.card (Bar2 L)) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hα) (orderOf_dvd_of_pow_eq_one hN)
  rw [((Nat.Prime.coprime_iff_not_dvd hr).2 hrL).gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff]
    at h1
  refine ⟨ha, fun l hl => ?_⟩
  have h2 : UC6S846.rhoL L m (QuotientGroup.mk ⟨l, hl⟩) = QuotientGroup.mk ⟨l, hl⟩ := by
    rw [h1, MulAut.one_apply]
  exact (UC6S846.rhoL_fix_iff L m ⟨l, hl⟩).1 h2

theorem uc22p2213a_not_le_centralizer (D : Data G) (Ch : Choice2011 G) (h117 : R117W D)
    (hV : S22_V D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hc2 : (conjSetOf D.M K).ncard = 2) : ¬ K ≤ centralizer (c.V : Set G) := by
  intro hKV
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hK.1
  have hKX : K ∈ calC (F11.CTilde D.M ⊥ c.V) := by
    rw [uc22p22u_cTilde_bot]
    exact uc22p22u_calC_of_le hK (le_inf hKM hKV) inf_le_left
  have hMK : D.M ≤ normalizer (K : Set G) :=
    (h117 c.V (uc22p22vd_hyp11 D Ch h1930 hV c) K hKX).1
  have hsub : conjSetOf D.M K ⊆ {K} := by
    rintro A ⟨g, hg, rfl⟩
    exact Set.mem_singleton_iff.2 (Subgroup.mem_normalizer_iff_map_conj_eq.1 (hMK hg))
  have := Set.ncard_le_ncard hsub (Set.finite_singleton K)
  rw [hc2, Set.ncard_singleton] at this
  omega

theorem uc22p2213a_false_of_odd_dvd (D : Data G) (Ch : Choice2011 G) (h117 : R117W D)
    (h869P : F08.R869NPair D) (hV : S22_V D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hc2 : (conjSetOf D.M K).ncard = 2) {n : ℕ}
    (hn2 : 2 < n) (hL2 : IsL2 (Bar2 K) n) (hpow : IsPowTwo n) {m : ℕ} (hmo : Odd m)
    (hm1 : 1 < m) (hmn : m ∣ c.n) : False := by
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hK.1
  have h4 : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd (show 2 ^ m - 1 ≠ 1 by omega)
  have hr2 : r ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    omega
  have hrpi : r ∈ piSet c.B0 := by
    rw [c.hpi]
    refine ⟨hr, hrm.trans ?_⟩
    have h := Nat.pow_sub_one_gcd_pow_sub_one 2 m c.n
    rw [Nat.gcd_eq_left hmn] at h
    rw [← h]
    exact Nat.gcd_dvd_right _ _
  have hrn : ¬ r ∣ n := by
    obtain ⟨j, rfl⟩ := hpow
    intro h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  have hrL : ∀ {X : Type} [Group X] [Finite X], IsL2 X n → ¬ r ∣ Nat.card X := by
    intro X _ _ hX h
    rw [uc22p22r_L2_card hX] at h
    rcases (Nat.Prime.dvd_mul hr).1 h with h1 | h1
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h1))
    · rw [← pow_mul] at h1
      have h2 : r ∣ Nat.gcd (2 ^ m - 1) (2 ^ (n * 2) - 1) := Nat.dvd_gcd hrm h1
      rw [Nat.pow_sub_one_gcd_pow_sub_one] at h2
      have hg : Nat.gcd m (n * 2) = 1 := by
        obtain ⟨j, rfl⟩ := hpow
        rw [← pow_succ]
        exact Nat.Coprime.pow_right _ hmo.coprime_two_right
      rw [hg, pow_one] at h2
      exact hr.not_dvd_one (by simpa using h2)
  obtain ⟨a, haB, hao⟩ := uc22p22i_exists_elt_of_mem_piSet hrpi
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hao
    exact hr.one_lt.ne hao
  have har : a ^ r = 1 := by
    rw [← hao]
    exact pow_orderOf_eq_one a
  have hfix := uc22p2214_fix D c hKM (Or.inr hc2)
  have hKV := uc22p2213a_not_le_centralizer D Ch h117 hV h1930 c hK hc2
  obtain ⟨K', hK', k, hk, hnot⟩ := uc22p2214_faith_of_normalizer_le D Ch hV h1930 c hK hKV
    (h869P K hK hc2 n hn2 hpow hL2) hfix haB ha1
  apply hnot
  have hK'C := uc22p2214_calC_of_mem_conjSetOf hK hK'
  have hL2' : IsL2 (Bar2 K') n := by
    obtain ⟨g, -, rfl⟩ := hK'
    obtain ⟨e⟩ := uc22p20d_bar2_conj g K
    exact CFSG.Blueprint.LieModel.of_mulEquiv e hL2
  have hcb := uc22p2213a_centralizesBar_of_prime hL2' hr hrn (hrL hL2') (hfix K' hK' haB) har
  exact uc22p22f_pCoreOf_le_cent hV h1930 c
    (uc22p22r_pCoreOf_le_of_isSubnormal hK'C.1 (hcb.2 k hk))

theorem uc22p2213a_false_of_not_isPowTwo (D : Data G) (Ch : Choice2011 G) (h117 : R117W D)
    (h869P : F08.R869NPair D) (hV : S22_V D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hc2 : (conjSetOf D.M K).ncard = 2) {n : ℕ}
    (hn2 : 2 < n) (hL2 : IsL2 (Bar2 K) n) (hpow : IsPowTwo n) (hn0 : ¬ IsPowTwo c.n) : False := by
  obtain ⟨k, m, hmo, hnk⟩ := Nat.exists_eq_two_pow_mul_odd (uc22p2213a_n_ne_zero D c.toCtx21)
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hn0 ⟨k, by rw [hnk, mul_one]⟩
  have hm0 : 0 < m := hmo.pos
  exact uc22p2213a_false_of_odd_dvd D Ch h117 h869P hV h1930 c hK hc2 hn2 hL2 hpow hmo
    (by omega) (Dvd.intro_left _ hnk.symm)

end CFSG.LocalAnalysis.UniquenessCase.UC22

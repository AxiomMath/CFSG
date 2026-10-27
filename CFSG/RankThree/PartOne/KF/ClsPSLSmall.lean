module

public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.RankThree.PartOne.KF.RankGL
public import CFSG.RankThree.PartOne.KF.R1Model

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.KFU

namespace KFU

theorem localRank_le_open_pRank {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) :
    localRank p G ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  refine csSup_le' ?_
  rintro _ ⟨H, -, rfl⟩
  exact CFSG.SectionRank.pRank_mono hp.one_lt le_top

variable {K : Type} [Field K] {n : ℕ}

theorem scalar_pow_of_det_eq_one {z : GL (Fin n) K} (hz : z ∈ StatedScalars (Fin n) K)
    (hdet : (z : Matrix (Fin n) (Fin n) K).det = 1) : z ^ n = 1 := by
  obtain ⟨c, rfl⟩ := hz
  have h1 : ((c : Kˣ) : K) ^ n = 1 := by
    have : ((Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K).det = (c : K) ^ n := by
      simp [Matrix.GeneralLinearGroup.scalar]
    rw [← this]
    exact hdet
  rw [← map_pow]
  have : c ^ n = 1 := Units.ext (by simpa using h1)
  rw [this, map_one]

theorem isCentralPQuot_statedSL_of_not_dvd [Finite K] {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    IsCentralPQuot p (QuotientGroup.mk'
      ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))) := by
  refine ⟨QuotientGroup.mk'_surjective _, ?_, ?_⟩
  · intro z hz
    rw [QuotientGroup.ker_mk'] at hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hzc : (z : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K) := by
      rw [← statedScalars_eq_center]
      exact hz
    exact Subgroup.mem_center_iff.mp hzc g
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hxk : (x : ↥(StatedSL n K)) ∈ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp x.2)
    have hxn : x ^ n = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      have := scalar_pow_of_det_eq_one (z := ((x : ↥(StatedSL n K)) : GL (Fin n) K)) hxk
        (mem_statedSL_iff.mp (x : ↥(StatedSL n K)).2)
      simpa using this
    have h3 := orderOf_dvd_of_pow_eq_one hxn
    rw [hx] at h3
    exact hpn h3

theorem localRank_statedProj_le [Finite K] {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : ¬ p ∣ n)
    (hbound : ∀ E : Subgroup (GL (Fin n) K), E ≤ StatedSL n K →
      (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) → (∀ g ∈ E, g ^ p = 1) → Nat.card E ≤ p ^ k) :
    localRank p (StatedProj (StatedSL n K)) ≤ k := by
  have hq := isCentralPQuot_statedSL_of_not_dvd (K := K) hp hpn
  have hcop : ¬ p ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) := by
    have := hq.coprime
    rw [QuotientGroup.ker_mk'] at this
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp this
  have h1 := CFSG.RankThree.Classical2.localRank_quotient_le hp hp2
    ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) hcop
  have h2 := localRank_le_open_pRank hp (G := ↥(StatedSL n K))
  have h3 := CFSG.RankThree.PartOne.LIT.pRank_le_of_card_gl hp.one_lt (StatedSL n K) hbound
  exact h1.trans (h2.trans h3)

end KFU

open KFU in
theorem psl_small_cases {G : Type} [Group G] [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Generic p L A₀ F) {n f : ℕ} (hn : n ≤ 4)
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f) :
    (n = 3 ∧ p ∣ 2 ^ f - 1) ∨ (n = 4 ∧ p ∣ 2 ^ f + 1) := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  have hn2 : 2 ≤ n := hadm.2.2.1
  have : Finite (StatedProj (StatedSL n K)) := Finite.of_equiv _ e.toEquiv
  have hX := h.localRank_eq_two_of_mulEquiv e
  have hp := h.prime
  have h5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [Fintype.card_eq_nat_card]; exact hK)
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have h1 := (CharP.cast_eq_zero_iff K 2 p).mp h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h1).symm
  have hpn : ¬ p ∣ n := fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hq1 : ¬ p ∣ 2 ^ f - 1 → ¬ p ∣ Nat.card K ^ 1 - 1 := by
    intro hdvd
    rwa [hK, pow_one]
  interval_cases n
  · exfalso
    have hle := localRank_statedProj_le (K := K) (n := 2) (k := 1) hp hp2 hpn (by
      intro E hE hcomm hexp
      have := LIT.card_le_of_det_eq_one_gl_two hp hpK (by simp) E hcomm hexp
        (fun g hg => mem_statedSL_iff.mp (hE hg))
      simpa using this)
    omega
  · by_cases hdvd : p ∣ 2 ^ f - 1
    · exact Or.inl ⟨rfl, hdvd⟩
    · exfalso
      have hle := localRank_statedProj_le (K := K) (n := 3) (k := 1) hp hp2 hpn (by
        intro E hE hcomm hexp
        have := LIT.card_le_pow_div_gl hp hpK (d := 2) (by norm_num) (by
          intro i hi0 hi2
          have hi1 : i = 1 := by omega
          subst hi1
          exact hq1 hdvd) E hcomm hexp
        simpa using this)
      omega
  · by_cases hm : p ∣ 2 ^ f - 1
    · exfalso
      have hrK : p ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; exact hm
      have h3 := CFSG.RankThree.PartTwo.Census.le_localRank_PSL_torus (K := K) (m := 3) (n := 4)
        hp hrK (by norm_num) (by norm_num) (Or.inr (fun hd => by
          have := Nat.le_of_dvd (by norm_num) hd
          omega))
      rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
        (projectiveSpecialLinearGroupEquivStatedProj 4 K) hp] at h3
      omega
    · by_cases hm1 : p ∣ 2 ^ f + 1
      · exact Or.inr ⟨rfl, hm1⟩
      · exfalso
        have hsq : ¬ p ∣ Nat.card K ^ 2 - 1 := by
          intro hd
          have hf1 : 1 ≤ f := hadm.2.1
          have h2f : 2 ≤ 2 ^ f := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
          have hfac : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
            have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
            zify [this, Nat.one_le_pow 2 (2 ^ f) (by omega)]
            ring
          rw [hK, hfac] at hd
          rcases hp.dvd_mul.mp hd with h1 | h1
          · exact hm h1
          · exact hm1 h1
        have hle := localRank_statedProj_le (K := K) (n := 4) (k := 1) hp hp2 hpn (by
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

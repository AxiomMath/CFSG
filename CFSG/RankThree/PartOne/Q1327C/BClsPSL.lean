module

public import CFSG.RankThree.PartOne.Q1327C.BDefs
public import CFSG.RankThree.PartOne.N143X.EvenExcl
public import CFSG.RankThree.PartOne.N143X.EvenOrders
public import CFSG.RankThree.PartOne.KF.ClsPSLBig
public import CFSG.RankThree.PartOne.KF.ClsPSLSmall
public import CFSG.RankThree.PartOne.Q1327C.BBase
public import CFSG.RankThree.PartOne.Q1327C.BRows

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PerfectCover
  CFSG.LocalAnalysis.ComponentInitial
open Matrix

variable {G : Type} [Group G] [Finite G] {p : ℕ} {X A₀ F : Subgroup G}

theorem pow_three_dvd_of_dvd_mul_five {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {a b m N : ℕ}
    (hN : N ∣ 2 ^ a * 3 ^ b * m) (h : p ^ 3 ∣ N) : p ^ 3 ∣ m := by
  have h1 : p ^ 3 ∣ 2 ^ a * 3 ^ b * m := h.trans hN
  have hcop : Nat.Coprime (p ^ 3) (2 ^ a * 3 ^ b) := by
    refine Nat.Coprime.mul_right ?_ ?_ <;>
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp (by norm_num)).2 (by omega))
  exact hcop.dvd_of_dvd_mul_left h1

theorem no_cube_dvd_gl5 {q : ℕ} (hq : 2 ≤ q) : ¬ q ^ 3 ∣ 5 * 7 * 31 := by
  intro h
  have : q ^ 3 ≤ 5 * 7 * 31 := Nat.le_of_dvd (by norm_num) h
  have hq11 : q ≤ 11 := by
    by_contra hc
    have : 12 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases q <;> omega

theorem no_cube_dvd_gl6 {q : ℕ} (hq : 2 ≤ q) : ¬ q ^ 3 ∣ 5 * (7 ^ 2 * 31) := by
  intro h
  have : q ^ 3 ≤ 5 * (7 ^ 2 * 31) := Nat.le_of_dvd (by norm_num) h
  have hq20 : q ≤ 20 := by
    by_contra hc
    have : 21 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases q <;> omega

theorem no_cube_dvd_gl7 {q : ℕ} (hq : 2 ≤ q) : ¬ q ^ 3 ∣ 5 * (7 ^ 2 * 31 * 127) := by
  intro h
  have : q ^ 3 ≤ 5 * (7 ^ 2 * 31 * 127) := Nat.le_of_dvd (by norm_num) h
  have hq99 : q ≤ 99 := by
    by_contra hc
    have : 100 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases q <;> omega

theorem false_of_psl_two_B {T : Type} [Group T] [Finite T] {n : ℕ} (hn : 5 ≤ n)
    (hmod : StatedClassicalModel T .PSL n 2 1) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hd : p ^ 3 ∣ Nat.card T) (he : evenRank T ≤ 3) : False := by
  by_cases hn8 : 8 ≤ n
  · exact N143X.false_of_psl_large hmod (Or.inr hn8) he
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
    have : Fintype K := Fintype.ofFinite K
    have hK2 : Fintype.card K = 2 := by rw [Fintype.card_eq_nat_card, hK]; norm_num
    have hdvd : p ^ 3 ∣ Nat.card (GL (Fin n) K) :=
      hd.trans (N143X.card_dvd_card_GL_of_stated _ e)
    rw [Matrix.card_GL_field, hK2] at hdvd
    have hn567 : n = 5 ∨ n = 6 ∨ n = 7 := by omega
    rcases hn567 with rfl | rfl | rfl
    · have : (∏ i : Fin 5, (2 ^ 5 - 2 ^ (i : ℕ))) = 2 ^ 10 * 3 ^ 2 * (5 * 7 * 31) := by
        simp [Fin.prod_univ_succ]
      rw [this] at hdvd
      exact no_cube_dvd_gl5 hp.two_le (pow_three_dvd_of_dvd_mul_five hp hp5 dvd_rfl hdvd)
    · have : (∏ i : Fin 6, (2 ^ 6 - 2 ^ (i : ℕ))) = 2 ^ 15 * 3 ^ 4 * (5 * (7 ^ 2 * 31)) := by
        simp [Fin.prod_univ_succ]
      rw [this] at hdvd
      exact no_cube_dvd_gl6 hp.two_le (pow_three_dvd_of_dvd_mul_five hp hp5 dvd_rfl hdvd)
    · have : (∏ i : Fin 7, (2 ^ 7 - 2 ^ (i : ℕ))) =
          2 ^ 21 * 3 ^ 4 * (5 * (7 ^ 2 * 31 * 127)) := by
        simp [Fin.prod_univ_succ]
      rw [this] at hdvd
      exact no_cube_dvd_gl7 hp.two_le (pow_three_dvd_of_dvd_mul_five hp hp5 dvd_rfl hdvd)

open KFU in
theorem psl_small_cases_B (h : Q1327.T123Base p X A₀ F) {n f : ℕ} (hn : n ≤ 4)
    (hmodel : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL n 2 f) :
    (n = 3 ∧ p ∣ 2 ^ f - 1) ∨ (n = 4 ∧ p ∣ 2 ^ f + 1) ∨ (n = 4 ∧ p ∣ 2 ^ f - 1) := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  have hn2 : 2 ≤ n := hadm.2.2.1
  have : Finite (StatedProj (StatedSL n K)) := Finite.of_equiv _ e.toEquiv
  have hX := T123Base.two_le_localRank_of_mulEquiv h e
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
    · exact Or.inr (Or.inr ⟨rfl, hm⟩)
    · by_cases hm1 : p ∣ 2 ^ f + 1
      · exact Or.inr (Or.inl ⟨rfl, hm1⟩)
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

open KFU in
theorem psl_large_false_B
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Q1327.T123Base p X A₀ F) {n f : ℕ} (hn : 5 ≤ n)
    (hmodel : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL n 2 f) : False := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  have hf1 : 1 ≤ f := hadm.2.1
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥X)) := T123Base.coprime_center h
  let e' : ↥X ⧸ Subgroup.center ↥X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm
  have hq := isCentralPQuot_center e' hcop
  have hLp : Group.IsPerfect ↥X := h.quasisimple.1
  obtain ⟨ρ, hρs, hρk⟩ := exists_cover_psl hGA hn hf1 hK hLp _ hq.surjective hq.central
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [Fintype.card_eq_nat_card]; exact hK)
  rcases Nat.lt_or_ge f 2 with hf | hf2
  · have hf1' : f = 1 := by omega
    subst hf1'
    have hcenSL : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) = ⊥ := by
      rw [← Subgroup.card_eq_one, ← LinearFlag.scalars_eq_center, card_scalars (by omega), hK]
      simp
    have hρinj : Function.Injective ρ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact eq_bot_iff.mpr (hρk.trans hcenSL.le)
    let ψ : Matrix.SpecialLinearGroup (Fin n) K ≃* ↥X := MulEquiv.ofBijective ρ ⟨hρinj, hρs⟩
    let π : Matrix.SpecialLinearGroup (Fin n) K →* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
      QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    have hπinj : Function.Injective π := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcenSL]
    let χ : Matrix.SpecialLinearGroup (Fin n) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
      MulEquiv.ofBijective π ⟨hπinj, QuotientGroup.mk'_surjective _⟩
    exact false_of_psl_two_B hn ⟨hadm, K, hKf, hKfin, hK,
      ⟨ψ.symm.trans (χ.trans (projectiveSpecialLinearGroupEquivStatedProj n K))⟩⟩ h.prime
      h.five_le (pow_three_dvd_card_X h) h.evenRank_le
  · obtain ⟨r, hr, hr2, hr5, hrd⟩ := exists_odd_prime_dvd_two_pow_sub_one_ne_five hf2
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
    have h3 := (CFSG.RankThree.OddKernel.localRank_le_evenRank hr hr2).trans h.evenRank_le
    omega

theorem bTag_PSL
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Q1327.T123Base p X A₀ F)
    (hLie : ∃ n f : ℕ, StatedLieAdmissible .PSL n 2 f ∧
      CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .PSL n 2 f) : BOutcome p X := by
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hcl : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL n 2 f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  rcases Nat.lt_or_ge n 5 with hn | hn
  · rcases psl_small_cases_B h (by omega) hcl with ⟨rfl, hp⟩ | ⟨rfl, hp⟩ | ⟨rfl, hp⟩
    · exact (false_of_row_rank_two h (r := 1) rfl
        (rowData_core_one (T123Base.toCore h) ⟨f, hadm.2.1, hp, hcl⟩)).elim
    · exact (false_of_row_rank_two h (r := 8) rfl
        (rowData_core_eight (T123Base.toCore h) ⟨f, hadm.2.1, hp, hcl⟩)).elim
    · exact BOutcome.of_L4 ⟨f, hadm.2.1, hp, hcl⟩
  · exact (psl_large_false_B hGA h hn hcl).elim

end CFSG.RankThree.PartOne.Q1327C

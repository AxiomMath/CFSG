module

public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.RankThree.PartOne.KF.FlagSplit
public import CFSG.LieType.BorelTits.Symplectic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LieType.Classical.SteinbergBLSymplectic

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem eq_one_of_sq_eq_one_charTwo {c : K} (h : c ^ 2 = 1) : c = 1 := by
  have hK2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hsq : (c - 1) ^ 2 = 0 := by linear_combination h + (1 - c) * hK2
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 hsq)

omit [Finite K] in
theorem statedScalars_subgroupOf_statedSp_eq_bot {n : ℕ} (hn : 1 ≤ n) :
    (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hx
  have hcS : Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c ∈ StatedSp n K := by
    rw [hc]
    exact x.2
  have hc1 : c = 1 := by
    have := eq_one_of_sq_eq_one_charTwo (c := (c : K))
      (by rw [← Units.val_pow_eq_pow_val, (CFSG.LieType.Classical.scalar_mem_statedSp_iff hn c).1
        hcS, Units.val_one])
    exact Units.ext this
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

noncomputable def spEquivProj {n : ℕ} (hn : 1 ≤ n) :
    ↥(StatedSp n K) ≃* StatedProj (StatedSp n K) :=
  MulEquiv.ofBijective
    (QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)))
    ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
      exact statedScalars_subgroupOf_statedSp_eq_bot hn, QuotientGroup.mk'_surjective _⟩

theorem localRank_statedProj_eq {n : ℕ} (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) :
    localRank p (StatedProj (StatedSp n K)) = localRank p ↥(StatedSp n K) :=
  (CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv (spEquivProj hn) hp).symm

omit [Finite K] in
theorem natCast_ne_zero_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (p : K) ≠ 0 := by
  intro h
  have := (CharP.cast_eq_zero_iff K 2 p).1 h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm

theorem exists_flag_of_two_le_localRank_statedSp {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : ℕ} (hd : 0 < d) (hdiv : ∀ i : ℕ, 0 < i → i < d → ¬ p ∣ Nat.card K ^ i - 1)
    (hrk : 2 ≤ localRank p ↥(StatedSp n K)) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ n ∧ 2 ≤ a / d + (2 * n - 2 * a) / d := by
  obtain ⟨U, hU2, hU0, E, hEU, hEel, hEc⟩ :=
    exists_elemAbelian_of_le_localRank hp (by omega : 1 ≤ 2) hrk
  have hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hEel.toIsMulCommutative.is_comm.comm (⟨g, hg⟩ : E) ⟨h, hh⟩)
  have hexp : ∀ g ∈ E, g ^ p = 1 := fun g hg =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian g hg
  obtain ⟨a, ha1, ha2, hcard⟩ := card_le_of_normalizes (spForm n K) (natRep (StatedSp n K))
    (isIsometric_natRep_statedSp n K) (natRep_injective _) hp hp2
    (natCast_ne_zero_of_ne_two hp hp2) hd hdiv hU2 hU0 hEU hcomm hexp
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin,
    show n + n = 2 * n by omega] at ha2 hcard
  rw [hEc, ← pow_add] at hcard
  exact ⟨a, ha1, by omega, (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard⟩

theorem localRank_statedSp_two_le_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h1 : ¬ p ∣ Nat.card K - 1) : localRank p ↥(StatedSp 2 K) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_flag_of_two_le_localRank_statedSp (K := K) hp hp2
    (d := 2) (by norm_num)
    (fun i hi hid => by
      obtain rfl : i = 1 := by omega
      simpa using h1) hlt
  omega

theorem not_dvd_sq_sub_one {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q) (h1 : ¬ p ∣ q - 1)
    (h2 : ¬ p ∣ q + 1) : ¬ p ∣ q ^ 2 - 1 := by
  intro h
  have e : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [show (k + 1) ^ 2 - 1 = k * (k + 2) by
      have : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
      omega]
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
  · exact h1 h'
  · exact h2 h'

theorem localRank_statedSp_three_le_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h1 : ¬ p ∣ Nat.card K - 1) (h2 : ¬ p ∣ Nat.card K + 1) :
    localRank p ↥(StatedSp 3 K) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_flag_of_two_le_localRank_statedSp (K := K) hp hp2
    (d := 3) (by norm_num)
    (fun i hi hid => by
      obtain rfl | rfl : i = 1 ∨ i = 2 := by omega
      · simpa using h1
      · exact not_dvd_sq_sub_one hp hq h1 h2) hlt
  omega

theorem localRank_statedSp_four_five_le_one (hK : Nat.card K = 2) :
    localRank 5 ↥(StatedSp 4 K) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_flag_of_two_le_localRank_statedSp (K := K)
    (by norm_num) (by norm_num) (d := 4) (by norm_num)
    (fun i hi hid => by
      rw [hK]
      interval_cases i <;> decide) hlt
  omega

theorem not_sq_dvd_card_sp_four {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ¬ p ^ 2 ∣ 2 ^ 16 * (3 * 15 * 63 * 255) := by
  intro h
  have e : 2 ^ 16 * (3 * 15 * 63 * 255) = 2 ^ 16 * (3 ^ 5 * 5 ^ 2 * 7 * 17) := by norm_num
  rw [e] at h
  have hpd : p ∣ 2 ^ 16 * (3 ^ 5 * 5 ^ 2 * 7 * 17) := (dvd_pow_self p two_ne_zero).trans h
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
    omega
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h4
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h4)
          omega
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hp.dvd_of_dvd_pow h4)
          omega
      · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).1 h3
        subst this
        norm_num at h
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)).1 h2
      subst this
      norm_num at h

omit [CharP K 2] in
theorem localRank_statedSp_four_seven_le_one (hK : Nat.card K = 2) {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) : localRank p ↥(StatedSp 4 K) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨U, hU2, hU0, E, hEU, hEel, hEc⟩ :=
    exists_elemAbelian_of_le_localRank hp (by omega : 1 ≤ 2) hlt
  have hdvd : p ^ 2 ∣ Nat.card ↥(StatedSp 4 K) := hEc ▸ Subgroup.card_subgroup_dvd_card E
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK] at hdvd
  have hprod : ∏ j ∈ Finset.Icc 1 4, (2 ^ (2 * j) - 1) = 3 * 15 * 63 * 255 := by decide
  rw [hprod] at hdvd
  exact not_sq_dvd_card_sp_four hp hp7 (by
    have : (2 : ℕ) ^ (4 ^ 2) = 2 ^ 16 := by norm_num
    rwa [this] at hdvd)

theorem localRank_statedSp_four_le_one (hK : Nat.card K = 2) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) : localRank p ↥(StatedSp 4 K) ≤ 1 := by
  rcases Nat.lt_or_ge p 7 with h7 | h7
  · obtain rfl : p = 5 := by
      interval_cases p
      · rfl
      · exact absurd hp (by norm_num)
    exact localRank_statedSp_four_five_le_one hK
  · exact localRank_statedSp_four_seven_le_one hK hp h7

end CFSG.RankThree.PartOne.KFU

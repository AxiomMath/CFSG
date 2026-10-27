module

public import CFSG.Quasithin.EmptyFaithful.S146zYFOPstd
public import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover

public section

namespace CFSG.Quasithin.S146zY

namespace FiveOdd

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem factorization_five_mul_sq {e R : ℕ} (he : e ≠ 0) (hR : R ≠ 0) (h5 : ¬ 5 ∣ R) :
    (e ^ 2 * R).factorization 5 = (e ^ 2).factorization 5 := by
  rw [Nat.factorization_mul (pow_ne_zero 2 he) hR, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h5, add_zero]

theorem not_five_dvd_plus {p : ℕ} (hp : p % 5 = 1) : ¬ 5 ∣ p ^ 3 * (p + 1) * (p ^ 2 + p + 1) := by
  have h2 : p ^ 2 % 5 = 1 := by simp [Nat.pow_mod, hp]
  have h3 : p ^ 3 % 5 = 1 := by simp [Nat.pow_mod, hp]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_five).1 hd with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h with h | h
    · have := Nat.mod_eq_zero_of_dvd h
      omega
    · have := Nat.mod_eq_zero_of_dvd h
      omega
  · have := Nat.mod_eq_zero_of_dvd h
    omega

theorem not_five_dvd_minus {p : ℕ} (hp : p % 5 = 4) (hp2 : p ≤ p ^ 2) :
    ¬ 5 ∣ p ^ 3 * (p - 1) * (p ^ 2 - p + 1) := by
  have h2 : p ^ 2 % 5 = 1 := by simp [Nat.pow_mod, hp]
  have h3 : p ^ 3 % 5 = 4 := by simp [Nat.pow_mod, hp]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_five).1 hd with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h with h | h
    · have := Nat.mod_eq_zero_of_dvd h
      omega
    · have := Nat.mod_eq_zero_of_dvd h
      omega
  · have := Nat.mod_eq_zero_of_dvd h
    omega

theorem fiveModel_statedSL [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : p % 5 = 1)
    (hK : Nat.card K = p) : FiveModel (StatedSL 3 K) ⊤ := by
  have hp2 := hp.two_le
  have hq1 : 1 ≤ p := by omega
  have hp0 : 0 < p := by omega
  have hM : Nat.card (⊤ : Subgroup Kˣ) = p - 1 := by rw [Subgroup.card_top, card_units_eq, hK]
  refine ⟨monomialData_statedSL, fun _ _ _ => Subgroup.mem_top _, ?_, ?_⟩
  · rw [card_statedSL_three, hK, hM]
    have e1 : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      zify [hq1, Nat.one_le_pow 2 _ hq1]
      ring
    have e2 : p ^ 3 - 1 = (p - 1) * (p ^ 2 + p + 1) := by
      zify [hq1, Nat.one_le_pow 3 _ hq1]
      ring
    rw [e1, e2, show p ^ 3 * ((p - 1) * (p + 1)) * ((p - 1) * (p ^ 2 + p + 1)) =
      (p - 1) ^ 2 * (p ^ 3 * (p + 1) * (p ^ 2 + p + 1)) by ring]
    exact factorization_five_mul_sq (by omega) (by positivity) (not_five_dvd_plus hp5)
  · rw [hM]
    omega

theorem fiveModel_statedSU [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : p % 5 = 4)
    (hK : Nat.card K = (p ^ 1) ^ 2) : FiveModel (StatedSU 3 (p ^ 1) K) (normOne K (p ^ 1)) := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  have hK' : Nat.card K = p ^ 2 := by rw [hK, pow_one]
  have hchar : CharP K p :=
    charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK'])
  have hp2 := hp.two_le
  have hq1 : 1 ≤ p := by omega
  have hqq : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  refine ⟨monomialData_statedSU, ?_, ?_, ?_⟩
  · intro d hd i
    have hu := unitary_of_mem_statedSU hK hd
    rw [coe_diagHom, Matrix.diagonal_map (by simp [hp.ne_zero]), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal] at hu
    have hii := congrFun (congrFun hu i) i
    rw [diagonal_apply_eq, Matrix.one_apply_eq] at hii
    rw [mem_normOne]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one]
    exact hii
  · rw [card_statedSU_three hK, card_normOne hK]
    simp only [pow_one]
    have e1 : p ^ 2 - 1 = (p + 1) * (p - 1) := by
      zify [hq1, Nat.one_le_pow 2 _ hq1]
      ring
    have e2 : p ^ 3 + 1 = (p + 1) * (p ^ 2 - p + 1) := by
      zify [hqq]
      ring
    rw [e1, e2, show p ^ 3 * ((p + 1) * (p - 1)) * ((p + 1) * (p ^ 2 - p + 1)) =
      (p + 1) ^ 2 * (p ^ 3 * (p - 1) * (p ^ 2 - p + 1)) by ring]
    exact factorization_five_mul_sq (by omega)
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hp.ne_zero) (by omega)) (Nat.succ_ne_zero _))
      (not_five_dvd_minus hp5 hqq)
  · rw [card_normOne hK, pow_one]
    omega

end FiveOdd

end CFSG.Quasithin.S146zY

namespace CFSG.Quasithin.S146zY

open FiveOdd

open CFSG.Assembly.LowTwoRank

theorem facts134Five_psl3Plus : ∀ p : ℕ, p.Prime → p % 5 = 1 →
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 p 1 := by
  intro p hp hp5
  refine noE25Config_of_oddLines fun X _ hX => ?_
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  exact E25OddLines.of_mulEquiv e (fiveModel_statedSL hp hp5 (by rw [hK, pow_one])).e25OddLines

theorem facts134Five_psu3Minus : ∀ p : ℕ, p.Prime → p % 5 = 4 →
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 p 1 := by
  intro p hp hp5
  refine noE25Config_of_oddLines fun X _ hX => ?_
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  exact E25OddLines.of_mulEquiv e (fiveModel_statedSU hp hp5 hK).e25OddLines

end CFSG.Quasithin.S146zY

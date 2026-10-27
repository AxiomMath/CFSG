module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OLineC
public import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover

public section

namespace CFSG.Quasithin.H13.NQCore.U3O

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank CFSG.Quasithin.F134.LieOdd

variable {K : Type} [Field K]

theorem factorization_sq_mul {e R p : ℕ} (he : e ≠ 0) (hR : R ≠ 0) (hp : ¬ p ∣ R) :
    (e ^ 2 * R).factorization p = (e ^ 2).factorization p := by
  rw [Nat.factorization_mul (pow_ne_zero 2 he) hR, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hp, add_zero]

theorem not_dvd_cofactor {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpk : p ∣ k + 3) :
    ¬ p ∣ (k + 2) ^ 3 * (k + 1) * (k ^ 2 + 3 * k + 3) := by
  intro hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · have h1 := hp.dvd_of_dvd_pow h
      have h2 : p ∣ 1 := (Nat.dvd_add_right h1).1 (by rwa [show k + 2 + 1 = k + 3 by ring])
      exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
    · have h2 : p ∣ 2 := (Nat.dvd_add_right h).1 (by rwa [show k + 1 + 2 = k + 3 by ring])
      have := Nat.le_of_dvd (by norm_num) h2
      omega
  · have h3 : p ∣ 3 := by
      have e : k ^ 2 + 3 * k + 3 = (k + 3) * k + 3 := by ring
      rw [e] at h
      exact (Nat.dvd_add_right (Dvd.dvd.mul_right hpk k)).1 h
    have := Nat.le_of_dvd (by norm_num) h3
    omega

theorem pModel_statedSU [Finite K] {r p : ℕ} (hr : r.Prime) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpr : p ∣ r + 1) (hK : Nat.card K = (r ^ 1) ^ 2) :
    PModel p (StatedSU 3 (r ^ 1) K) (normOne K (r ^ 1)) := by
  have : Fact r.Prime := ⟨hr⟩
  have := Fintype.ofFinite K
  have hK' : Nat.card K = r ^ 2 := by rw [hK, pow_one]
  have hchar : CharP K r :=
    charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK'])
  have hr2 := hr.two_le
  refine ⟨monomialData_statedSU, ?_, ?_, ?_⟩
  · intro d hd i
    have hu := unitary_of_mem_statedSU hK hd
    rw [coe_diagHom, Matrix.diagonal_map (by simp [hr.ne_zero]), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal] at hu
    have hii := congrFun (congrFun hu i) i
    rw [diagonal_apply_eq, Matrix.one_apply_eq] at hii
    rw [mem_normOne]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one]
    exact hii
  · rw [card_statedSU_three hK, card_normOne hK]
    simp only [pow_one]
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    have e1 : (k + 2) ^ 2 - 1 = (k + 1) * (k + 3) := by
      have : (k + 2) ^ 2 = (k + 1) * (k + 3) + 1 := by ring
      omega
    have e2 : (k + 2) ^ 3 + 1 = (k + 3) * (k ^ 2 + 3 * k + 3) := by ring
    rw [e1, e2, show (k + 2) ^ 3 * ((k + 1) * (k + 3)) * ((k + 3) * (k ^ 2 + 3 * k + 3)) =
      (k + 2 + 1) ^ 2 * ((k + 2) ^ 3 * (k + 1) * (k ^ 2 + 3 * k + 3)) by ring]
    exact factorization_sq_mul (by omega) (by positivity)
      (not_dvd_cofactor hp hp5 (by simpa [show k + 2 + 1 = k + 3 by ring] using hpr))
  · rw [card_normOne hK, pow_one]
    exact hpr

theorem pTorusProp_of_model {X : Type} [Group X] {r p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpr : p ∣ r + 1) (hX : StatedClassicalModel X .PSU 3 r 1) : PTorusProp p X := by
  obtain ⟨⟨hr, -⟩, K, _, _, hK, ⟨e⟩⟩ := hX
  have : Fact p.Prime := ⟨hp⟩
  exact PTorusProp.of_mulEquiv e ((pModel_statedSU hr hp hp5 hpr hK).torusProp hp5)

end CFSG.Quasithin.H13.NQCore.U3O

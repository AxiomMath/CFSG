module

public import CFSG.Quasithin.Background.HSL
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Open Subgroup

variable {K : Type} [Field K] [Finite K]

theorem s16h_H5_natNorm_statedSL_two_four_elemAbelian
    (hK : Nat.card K = 4) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {D : Subgroup (MulAut (StdMod (Fin 2) K))}
    (hDN : D ≤ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K))
    (hD : IsElemAbelian q D) :
    Nat.card D ≤ q ^ 2 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hΓ : HasScalarCommutant (CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
    hasScalarCommutant_statedSL (K := K) (by norm_num)
  have hAut : Nat.card (K ≃+* K) = 2 := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      (p := 2) (n := 2) Nat.prime_two K (by rw [hK]; norm_num)).1
    simpa using h
  let φ : ↥D →* (K ≃+* K) := (fieldHom hΓ).comp (Subgroup.inclusion hDN)
  have hφ1 : φ = 1 := by
    refine MonoidHom.ext fun d => ?_
    have hdq : d ^ q = 1 := Subtype.ext (hD.2 d d.2)
    have hq_dvd : orderOf (φ d) ∣ q :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [← map_pow, hdq, map_one])
    have h2_eq : (φ d) ^ 2 = 1 := by
      have := pow_card_eq_one' (x := φ d)
      rwa [hAut] at this
    have h2_dvd : orderOf (φ d) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2_eq
    rcases (Nat.dvd_prime hq).mp hq_dvd with h1 | hq_eq
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      rw [hq_eq] at h2_dvd
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2_dvd)
  have hDlin : D ≤ linSub (ι := Fin 2) (K := K) := by
    intro d hd
    have hφd : (fieldHom hΓ) ((Subgroup.inclusion hDN) ⟨d, hd⟩) = 1 := by
      have h := congrFun (congrArg DFunLike.coe hφ1) ⟨d, hd⟩
      exact h
    have hφd' : (fieldHom hΓ) (⟨d, hDN hd⟩ :
        ↥(natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K))) = 1 := by
      rwa [show (Subgroup.inclusion hDN) ⟨d, hd⟩ = ⟨d, hDN hd⟩ from rfl] at hφd
    exact (fieldHom_eq_one_iff hΓ ⟨d, hDN hd⟩).mp hφd'
  have hdiv : Nat.card D ∣ 180 := by
    have h1 : Nat.card D ∣ Nat.card (linSub (ι := Fin 2) (K := K)) := Subgroup.card_dvd_of_le hDlin
    have hlin : Nat.card (linSub (ι := Fin 2) (K := K)) = 180 := by
      have hrange : (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)).range =
          linSub (ι := Fin 2) (K := K) := by
        ext g
        constructor
        · rintro ⟨A, rfl⟩
          exact isSemilinear_matAut A
        · intro hg
          obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub hg
          exact ⟨A, rfl⟩
      rw [← hrange]
      rw [← Nat.card_congr (MonoidHom.ofInjective
        (f := (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K))) matHom_injective).toEquiv]
      rw [Matrix.card_GL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card, hK]
      norm_num
    rwa [hlin] at h1
  haveI : Fact q.Prime := ⟨hq⟩
  have hpg : IsPGroup q D := by
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (hD.2 x.1 x.2)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
  rw [hk] at hdiv
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk, hk0, pow_zero]
    exact Nat.one_le_pow 2 q hq.one_le
  · have hdvd : q ∣ 180 := dvd_trans (dvd_pow_self q hkpos.ne') hdiv
    have h235 : q = 2 ∨ q = 3 ∨ q = 5 := by
      have h180 : (180 : ℕ) = 2 ^ 2 * (3 ^ 2 * 5) := by norm_num
      rw [h180] at hdvd
      rcases hq.dvd_mul.mp hdvd with h2 | h'
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2))
      · rcases hq.dvd_mul.mp h' with h3 | h5
        · exact Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h3)))
        · exact Or.inr (Or.inr
            ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp h5))
    have hq3 : ¬ q ^ 3 ∣ 180 := by
      rcases h235 with rfl | rfl | rfl
      · exact absurd rfl hq2
      · norm_num
      · norm_num
    by_contra hle
    have hgt : q ^ 2 < q ^ k := by rw [← hk]; exact not_le.mp hle
    have hk3 : 3 ≤ k := by
      have := (Nat.pow_lt_pow_iff_right hq.one_lt).mp hgt
      omega
    exact hq3 (dvd_trans (pow_dvd_pow q hk3) hdiv)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

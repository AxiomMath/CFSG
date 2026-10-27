module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.Quasithin.Vol2.Ch10SecAShape

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

theorem center_SL_two_eq_bot (K : Type) [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center, eq_bot_iff]
  rintro A ⟨c, hc, hA⟩
  have hc2 : (c : K) * (c : K) = 1 := by
    rw [← sq, ← Units.val_pow_eq_pow_val, hc, Units.val_one]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hc1 : (c : K) = 1 := by
    have : ((c : K) - 1) * ((c : K) - 1) = 0 := by linear_combination hc2 - ((c : K) - 1) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  rw [hA, hc1]
  simp

noncomputable def slTwoEquivPSL (K : Type) [Field K] [CharP K 2] :
    Matrix.SpecialLinearGroup (Fin 2) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  ((QuotientGroup.quotientMulEquivOfEq (center_SL_two_eq_bot K)).trans
    QuotientGroup.quotientBot).symm

theorem dvd_two_pow_of_isPGroup {P : Type} [Group P] [Finite P] (hP : IsPGroup 2 P) {n b : ℕ}
    (hb : Odd b) (h : Nat.card P ∣ 2 ^ n * b) : Nat.card P ∣ 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hP)
  rw [hk] at h ⊢
  exact (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hb)).dvd_of_dvd_mul_right h

theorem alt4_sq : ∀ g : ↥(alternatingGroup (Fin 4)), g ^ 4 = 1 → g ^ 2 = 1 := by
  decide

theorem card_alt4_sq :
    Fintype.card {g : ↥(alternatingGroup (Fin 4)) // g ^ 2 = 1} = 4 := by
  decide

theorem card_psl_galois {m : ℕ} (hm : m ≠ 0) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) =
      2 ^ m * (4 ^ m - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.card_congr (slTwoEquivPSL (GaloisField 2 m)).toEquiv]
  exact card_SL_two_pow (GaloisField.card 2 m hm)

theorem card_pgl_galois_dvd {m : ℕ} (hm : m ≠ 0) :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField 2 m)) ∣
      2 ^ m * ((2 ^ m - 1) * (4 ^ m - 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := GaloisField.card 2 m hm
  have hdvd : Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField 2 m)) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 m)) :=
    Subgroup.card_quotient_dvd_card _
  have := Fintype.ofFinite (GaloisField 2 m)
  rw [Matrix.card_GL_field, Fin.prod_univ_two] at hdvd
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one] at hdvd
  rw [← Nat.card_eq_fintype_card, hc] at hdvd
  have h4 : (2 ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h1 : (2 ^ m) ^ 2 - 2 ^ m = 2 ^ m * (2 ^ m - 1) := by rw [Nat.mul_sub_one, sq]
  rw [h1, h4] at hdvd
  exact hdvd.trans (dvd_of_eq (by ring))

end CFSG.Quasithin.Vol2.Ch10.SecA

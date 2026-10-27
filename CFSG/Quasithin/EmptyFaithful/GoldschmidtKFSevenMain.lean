module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFSevenGr
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral

public section

namespace CFSG.Quasithin.SBd19F

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

theorem charP_seven_of_card [Finite K] (hk : Nat.card K = 7) : CharP K 7 := by
  have := Fintype.ofFinite K
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpp : p.Prime := CharP.char_is_prime K p
  obtain ⟨n, hn, hpn⟩ := FiniteField.card K p
  have h7 : p ^ (n : ℕ) = 7 := by rw [← hpn, ← Nat.card_eq_fintype_card, hk]
  have hn1 : 0 < (n : ℕ) := n.pos
  have hdvd : p ∣ 7 := h7 ▸ dvd_pow_self p hn1.ne'
  have : p = 7 := (Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp hdvd
  rw [this] at hp
  exact hp

theorem two_ne_zero_of_card_seven [Finite K] (hk : Nat.card K = 7) : (2 : K) ≠ 0 := by
  have := charP_seven_of_card hk
  intro h
  have := (CharP.cast_eq_zero_iff K 7 2).mp (by exact_mod_cast h)
  omega

theorem ringEquiv_eq_one_of_card_seven [Finite K] (hk : Nat.card K = 7) (σ : K ≃+* K) :
    σ = 1 := by
  have := charP_seven_of_card hk
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let φ : ZMod 7 →+* K := ZMod.castHom (dvd_refl 7) K
  have hφ : Function.Injective φ := φ.injective
  have hcard : Nat.card K ≤ Nat.card (ZMod 7) := by
    rw [hk, Nat.card_zmod]
  have hsurj : Function.Surjective φ := (hφ.bijective_of_nat_card_le hcard).2
  ext x
  obtain ⟨z, rfl⟩ := hsurj x
  have : (σ.toRingHom.comp φ) = φ := RingHom.ext_zmod _ _
  exact congrArg (fun f : ZMod 7 →+* K => f z) this

theorem not_isSolvable_fixedSub_of_sq [Finite K] (hk : Nat.card K = 7)
    (α : MulAut (projectiveSL 3 K)) (hα : α * α = 1) :
    ¬ Group.IsSolvable ↥(SBd18.fixedSub α) := by
  classical
  have hK4 : 4 ≤ Nat.card K := by rw [hk]; norm_num
  have h2 := two_ne_zero_of_card_seven hk
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 α
  have hσ : σ = 1 := ringEquiv_eq_one_of_card_seven hk σ
  rw [hσ, map_one, mul_one] at hα ⊢
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hα ⊢
    have hAA : conjAut 3 K (A * A) = 1 := by rw [map_mul]; exact hα
    obtain ⟨u, hu⟩ := (ProjectivePlane.conjAut_eq_one_iff (by norm_num) (A * A)).mp hAA
    exact not_isSolvable_fixedSub_conjAut hK4 h2 A u hu
  · rw [pow_one] at hα ⊢
    have htr := standard_automorphism_transport (K := K) (n := 3)
    have hδδ : dualAut 3 K * dualAut 3 K = 1 := htr.2.2.2.1
    have hδc : ∀ X : GL (Fin 3) K, dualAut 3 K * conjAut 3 K X * dualAut 3 K =
        conjAut 3 K (Matrix.GeneralLinearGroup.inverseTranspose X) := htr.2.2.2.2.1
    have hAA : conjAut 3 K (A * Matrix.GeneralLinearGroup.inverseTranspose A) = 1 := by
      rw [map_mul, ← hδc A, ← hα]
      calc conjAut 3 K A * (dualAut 3 K * conjAut 3 K A * dualAut 3 K)
          = conjAut 3 K A * dualAut 3 K * conjAut 3 K A * dualAut 3 K := by group
        _ = conjAut 3 K A * dualAut 3 K * (conjAut 3 K A * dualAut 3 K) := by group
    obtain ⟨u, hu⟩ := (ProjectivePlane.conjAut_eq_one_iff (by norm_num)
      (A * Matrix.GeneralLinearGroup.inverseTranspose A)).mp hAA
    have hdetA : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det (A : Matrix (Fin 3) (Fin 3) K)).mp A.isUnit).ne_zero
    have hX : (A : Matrix (Fin 3) (Fin 3) K) = (u : K) • (A : Matrix (Fin 3) (Fin 3) K)ᵀ := by
      have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hu
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_inverseTranspose,
        GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal] at h1
      have h2' : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *
          (A : Matrix (Fin 3) (Fin 3) K)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
      calc (A : Matrix (Fin 3) (Fin 3) K)
          = (A : Matrix (Fin 3) (Fin 3) K) * (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *
            (A : Matrix (Fin 3) (Fin 3) K)ᵀ) := by rw [h2', mul_one]
        _ = ((A : Matrix (Fin 3) (Fin 3) K) *
            ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ) *
              (A : Matrix (Fin 3) (Fin 3) K)ᵀ := by rw [mul_assoc]
        _ = (u : K) • (A : Matrix (Fin 3) (Fin 3) K)ᵀ := by rw [h1, Matrix.smul_mul, one_mul]
    have hX2 : (A : Matrix (Fin 3) (Fin 3) K) = ((u : K) * u) • (A : Matrix (Fin 3) (Fin 3) K) := by
      have := congrArg Matrix.transpose hX
      rw [Matrix.transpose_smul, Matrix.transpose_transpose] at this
      conv_lhs => rw [hX, this]
      rw [smul_smul]
    have huu : (u : K) * u = 1 := by
      by_contra hne
      have h0 : ((1 : K) - (u : K) * u) • (A : Matrix (Fin 3) (Fin 3) K) = 0 := by
        rw [sub_smul, one_smul, ← hX2, sub_self]
      have hdet0 := congrArg Matrix.det h0
      rw [Matrix.det_smul, Matrix.det_zero] at hdet0
      simp only [Fintype.card_fin] at hdet0
      rcases mul_eq_zero.mp hdet0 with h | h
      · exact hne (sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp h)).symm
      · exact hdetA h
    have hu1 : (u : K) = 1 := by
      rcases mul_self_eq_one_iff.mp huu with h | h
      · exact h
      · exfalso
        have hdet := congrArg Matrix.det hX
        rw [h, Matrix.det_smul, Matrix.det_transpose] at hdet
        simp only [Fintype.card_fin] at hdet
        apply hdetA
        have : (2 : K) * (A : Matrix (Fin 3) (Fin 3) K).det = 0 := by linear_combination hdet
        exact (mul_eq_zero.mp this).resolve_left h2
    have hAs : (A : Matrix (Fin 3) (Fin 3) K)ᵀ = A := by
      rw [hu1, one_smul] at hX
      exact hX.symm
    exact not_isSolvable_fixedSub_conjAut_dualAut hK4 h2 A hAs

end CFSG.Quasithin.SBd19F

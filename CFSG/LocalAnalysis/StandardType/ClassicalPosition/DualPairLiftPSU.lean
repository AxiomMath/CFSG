module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSU
public import CFSG.LocalAnalysis.StandardType.GGSixTCLiftGroup

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.LieType.Universal

private lemma dplPSU_conjTr_smul {F : Type} [Field F] (σ : F ≃+* F) {n : ℕ} (c : F)
    (A : Matrix (Fin n) (Fin n) F) :
    Unitary.conjTr σ (c • A) = σ c • Unitary.conjTr σ A := by
  ext i j
  simp [Unitary.conjTr, Matrix.map_apply]

private lemma dplPSU_scalar_of_conj {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {d : X} {A s : GL (Fin n) F}
    (hA : IsGLLift
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ A d)
    (hs : IsGLLift
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ s d) :
    ∃ z : F, (A : Matrix (Fin n) (Fin n) F) = z • (s : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨z, hz⟩ := isGLLift_unique_PSU hc n ψ hψ hA hs
  refine ⟨z, ?_⟩
  have h1 : (s : Matrix (Fin n) (Fin n) F) *
      ((s⁻¹ * A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (A : Matrix (Fin n) (Fin n) F) := by
    rw [← Units.val_mul]
    exact congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F))
      (show s * (s⁻¹ * A) = A by group)
  calc (A : Matrix (Fin n) (Fin n) F)
      = (s : Matrix (Fin n) (Fin n) F) *
          ((s⁻¹ * A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := h1.symm
    _ = (s : Matrix (Fin n) (Fin n) F) * Matrix.scalar (Fin n) z := by rw [hz]
    _ = z • (s : Matrix (Fin n) (Fin n) F) := by
        rw [Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal]

private lemma dplPSU_scalar_pow_eq_one {F : Type} [Field F] {n p : ℕ} (hn : 1 ≤ n)
    {g s : GL (Fin n) F} {z : F}
    (hconj : ((g * s * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      z • (s : Matrix (Fin n) (Fin n) F))
    (hsp : ∃ c : F, (s : Matrix (Fin n) (Fin n) F) ^ p = Matrix.scalar (Fin n) c) :
    z ^ p = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hLunit : IsUnit (((g * s * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    ⟨g * s * g⁻¹, rfl⟩
  have hzne : z ≠ 0 := by
    intro hz0
    rw [hconj, hz0, zero_smul] at hLunit
    exact hLunit.ne_zero rfl
  set Z : GL (Fin n) F := Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 z hzne) with hZ
  have hZcoe : (Z : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) z := by
    rw [hZ, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  have hZeq : Z * s = g * s * g⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, hZcoe, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, hconj]
  have hspc : ∀ A : GL (Fin n) F, A * s ^ p = s ^ p * A := by
    intro A
    obtain ⟨c, hc⟩ := hsp
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, hc]
    exact (Matrix.scalar_commute c (fun r' => Commute.all c r')
      (A : Matrix (Fin n) (Fin n) F)).eq.symm
  have hcommZs : Commute Z s := by
    rw [commute_iff_eq, hZ]
    exact Matrix.GeneralLinearGroup.scalar_commute (Units.mk0 z hzne) s
  have hconjpow : (g * s * g⁻¹ : GL (Fin n) F) ^ p = s ^ p := by
    rw [conj_pow, hspc g]
    group
  have hZp : Z ^ p = 1 := by
    have h1 : (Z * s) ^ p = (g * s * g⁻¹) ^ p := by rw [hZeq]
    rw [hconjpow, hcommZs.mul_pow p] at h1
    have h3 := congrArg (fun x : GL (Fin n) F => x * (s ^ p)⁻¹) h1
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using h3
  have hmatrix : Matrix.scalar (Fin n) (z ^ p) = 1 := by
    have h := congrArg (fun A : GL (Fin n) F => (A : Matrix (Fin n) (Fin n) F)) hZp
    rw [Units.val_pow_eq_pow_val, Units.val_one, hZcoe, ← map_pow] at h
    exact h
  exact Matrix.scalar_inj.mp (by rw [hmatrix, map_one])

private lemma dplPSU_scalar_norm {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hn : 1 ≤ n) {g s : GL (Fin n) F} {z : F}
    (hgU : Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (g : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (g : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hsU : Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hconj : ((g * s * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      z • (s : Matrix (Fin n) (Fin n) F)) :
    z ^ (2 ^ f + 1) = 1 := by
  haveI : NeZero n := ⟨by omega⟩
  have hgI : InnerDiagSU.IsJUnitary (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) g := hgU
  have hsI : InnerDiagSU.IsJUnitary (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) s := hsU
  have hgsgI : InnerDiagSU.IsJUnitary (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (g * s * g⁻¹) := (hgI.mul hsI).mul hgI.inv
  have hunit : Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      ((g * s * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n *
      ((g * s * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n := hgsgI
  rw [hconj, dplPSU_conjTr_smul] at hunit
  have hanti : z • (CFSG.LieType.BorelTits.unitaryInvolution F 2 f z •
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F)) = Unitary.antidiag n := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_smul] at hunit
    rw [hsU] at hunit
    exact hunit
  have hentry : z * CFSG.LieType.BorelTits.unitaryInvolution F 2 f z = 1 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M 0 (Fin.rev 0)) hanti
    have hJ : (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) 0 (Fin.rev 0) = 1 := by
      simp [Unitary.antidiag]
    simpa [Matrix.smul_apply, hJ] using h
  have hsig : CFSG.LieType.BorelTits.unitaryInvolution F 2 f z = z ^ 2 ^ f :=
    CFSG.LieType.BorelTits.unitaryInvolution_apply F 2 f z
  have hfull : z * z ^ (2 ^ f) = 1 := by rw [← hsig]; exact hentry
  rw [pow_succ']
  exact hfull

private lemma dplPSU_z_eq_one {F : Type} [Field F] {f p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ f - 1) (hf : 1 ≤ f) {z : F} (hzp : z ^ p = 1)
    (hzn : z ^ (2 ^ f + 1) = 1) : z = 1 := by
  have h2f : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hnotdvd : ¬ p ∣ 2 ^ f + 1 := by
    intro hdvd
    have hsub : p ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub hdvd hpq
    have h2 : p ∣ 2 := by
      rwa [show (2 ^ f + 1) - (2 ^ f - 1) = 2 by omega] at hsub
    have hp2 : p = 2 := by
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      have hge : 2 ≤ p := hp.two_le
      omega
    subst hp2
    have hodd : Odd (2 ^ f - 1) := by
      obtain ⟨k, hk⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
      subst hk
      have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ]
      exact ⟨2 ^ k - 1, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpq)
  have hcop : Nat.Coprime p (2 ^ f + 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnotdvd
  have hdvdp : orderOf z ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hzp
  have hdvdn : orderOf z ∣ 2 ^ f + 1 := orderOf_dvd_iff_pow_eq_one.mpr hzn
  have hg : orderOf z ∣ Nat.gcd p (2 ^ f + 1) := Nat.dvd_gcd hdvdp hdvdn
  rw [hcop.gcd_eq_one] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

theorem commute_adjoin_of_isGLLift_PSU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f - 1)
    (hsp : ∀ s ∈ S, ∃ c : F, (s : Matrix (Fin n) (Fin n) F) ^ p = Matrix.scalar (Fin n) c)
    (D : Subgroup X)
    (hSlift : ∀ s ∈ S, ∃ d ∈ D, IsGLLift
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ s d)
    {b : X} (hbD : ∀ d ∈ D, b * d = d * b) {g : GL (Fin n) F}
    (hgU : Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (g : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (g : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hg : IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ g b) :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S),
      (g : Matrix (Fin n) (Fin n) F) * a = a * (g : Matrix (Fin n) (Fin n) F) := by
  have hf : 1 ≤ f := by
    have hcard : 1 < Nat.card F := by
      haveI : Fintype F := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    by_contra h
    have hf0 : f = 0 := by omega
    subst hf0
    rw [hc] at hcard
    norm_num at hcard
  have hgen : ∀ s ∈ S, (g : Matrix (Fin n) (Fin n) F) * (s : Matrix (Fin n) (Fin n) F) =
      (s : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) := by
    intro s hs
    by_cases hn0 : n = 0
    · subst hn0
      exact Subsingleton.elim _ _
    · have hn : 1 ≤ n := Nat.pos_of_ne_zero hn0
      haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      obtain ⟨d, hdD, hsd⟩ := hSlift s hs
      have hg_inv : IsGLLift
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ g⁻¹ b⁻¹ :=
        IsGLLift.inv_of_injective (Subgroup.subtype_injective _) hg
      have h1 := hg_inv.mul hsd
      have h2 := h1.mul hg
      have hA : IsGLLift
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ
          (g * s * g⁻¹) d := by
        have hbd : b⁻¹ * d * b = d := by
          rw [show b⁻¹ * d * b = b⁻¹ * (d * b) by group, ← hbD d hdD]
          group
        rwa [show g * (s * g⁻¹) = g * s * g⁻¹ by group, hbd] at h2
      obtain ⟨z, hz⟩ := dplPSU_scalar_of_conj hc n ψ hψ hA hsd
      have hzp : z ^ p = 1 := dplPSU_scalar_pow_eq_one hn hz (hsp s hs)
      have hzn : z ^ (2 ^ f + 1) = 1 := dplPSU_scalar_norm hn hgU (hSU s hs) hz
      have hz1 : z = 1 := dplPSU_z_eq_one hp hpq hf hzp hzn
      have hAg : ((g * s * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
          (s : Matrix (Fin n) (Fin n) F) := by
        rw [hz, hz1, one_smul]
      have hgl : g * s * g⁻¹ = s := by
        apply Units.ext
        exact hAg
      have hcomm : g * s = s * g := by
        calc g * s = g * s * g⁻¹ * g := by group
          _ = s * g := by rw [hgl]
      simpa only [Units.val_mul] using
        congrArg (fun A : GL (Fin n) F => (A : Matrix (Fin n) (Fin n) F)) hcomm
  intro a ha
  refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute
    (a := (g : Matrix (Fin n) (Fin n) F)) ha ?_).eq
  rintro x ⟨s, hs, rfl⟩
  exact hgen s hs

end CFSG.StandardType.ClassicalPosition

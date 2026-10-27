module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSU
public import CFSG.LocalAnalysis.StandardType.GGE0LiftGeneric

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType.ClassicalPosition
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Universal.Unitary (conjTr antidiag)

private lemma isJUnitary_mul {n : ℕ} {F : Type} [Field F] {σ : F ≃+* F}
    {A B : Matrix (Fin n) (Fin n) F}
    (hA : conjTr σ A * antidiag n * A = antidiag n)
    (hB : conjTr σ B * antidiag n * B = antidiag n) :
    conjTr σ (A * B) * antidiag n * (A * B) = antidiag n := by
  rw [CFSG.LieType.Universal.Unitary.conjTr_mul σ]
  calc conjTr σ B * conjTr σ A * antidiag n * (A * B)
      = conjTr σ B * (conjTr σ A * antidiag n * A) * B :=
        by simp only [Matrix.mul_assoc]
    _ = conjTr σ B * antidiag n * B := by rw [hA]
    _ = antidiag n := hB

private lemma isJUnitary_inv {n : ℕ} {F : Type} [Field F] {σ : F ≃+* F}
    {M : Matrix (Fin n) (Fin n) F} (hM : M * M⁻¹ = 1)
    (hA : conjTr σ M * antidiag n * M = antidiag n) :
    conjTr σ M⁻¹ * antidiag n * M⁻¹ = antidiag n := by
  have h1 : conjTr σ M⁻¹ * conjTr σ M = 1 := by
    rw [← CFSG.LieType.Universal.Unitary.conjTr_mul σ, hM,
      CFSG.LieType.Universal.Unitary.conjTr_one σ]
  have hstar : conjTr σ M⁻¹ = (conjTr σ M)⁻¹ := (Matrix.inv_eq_left_inv h1).symm
  have hleft : (conjTr σ M)⁻¹ * conjTr σ M = 1 := by
    rw [← hstar]
    exact h1
  have h2 : (conjTr σ M)⁻¹ * antidiag n * M⁻¹ = antidiag n := by
    have hL : (conjTr σ M)⁻¹ * (conjTr σ M * antidiag n * M) * M⁻¹ = antidiag n := by
      simp only [Matrix.mul_assoc]
      rw [hM, Matrix.mul_one, ← Matrix.mul_assoc, hleft, Matrix.one_mul]
    have h := congrArg (fun N : Matrix (Fin n) (Fin n) F => (conjTr σ M)⁻¹ * N * M⁻¹) hA
    rw [hL] at h
    exact h.symm
  rw [hstar]
  exact h2

private lemma isJUnitary_commutator {n : ℕ} {F : Type} [Field F] {σ : F ≃+* F}
    {s t : GL (Fin n) F}
    (hs : conjTr σ (s : Matrix (Fin n) (Fin n) F) * antidiag n *
      (s : Matrix (Fin n) (Fin n) F) = antidiag n)
    (ht : conjTr σ (t : Matrix (Fin n) (Fin n) F) * antidiag n *
      (t : Matrix (Fin n) (Fin n) F) = antidiag n) :
    conjTr σ (((t * s)⁻¹ * (s * t) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * antidiag n *
      (((t * s)⁻¹ * (s * t) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = antidiag n := by
  have hts : conjTr σ (((t * s) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * antidiag n *
      (((t * s) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = antidiag n := by
    rw [Units.val_mul]
    exact isJUnitary_mul ht hs
  have hright : (((t * s) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((((t * s) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))⁻¹ = 1 := by
    rw [← Matrix.coe_units_inv]
    exact Units.mul_inv (t * s)
  have htsinv : conjTr σ (((t * s)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * antidiag n *
      (((t * s)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = antidiag n := by
    rw [Matrix.coe_units_inv]
    exact isJUnitary_inv hright hts
  have hst : conjTr σ (((s * t) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * antidiag n *
      (((s * t) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = antidiag n := by
    rw [Units.val_mul]
    exact isJUnitary_mul hs ht
  have h2 := isJUnitary_mul htsinv hst
  rwa [← Units.val_mul] at h2

private lemma scalar_mul_eq_one_of_isJUnitary {n : ℕ} {F : Type} [Field F] {σ : F ≃+* F}
    {a : F} (hn : 0 < n)
    (h : conjTr σ (Matrix.scalar (Fin n) a) * antidiag n * Matrix.scalar (Fin n) a =
      antidiag n) :
    σ a * a = 1 := by
  have : NeZero n := ⟨hn.ne'⟩
  have hstar : conjTr σ (Matrix.scalar (Fin n) a) = Matrix.scalar (Fin n) (σ a) := by
    ext i j
    by_cases hij : i = j
    · simp [CFSG.LieType.Universal.Unitary.conjTr, Matrix.scalar, Matrix.diagonal, hij]
    · have hji : ¬ j = i := fun h' => hij h'.symm
      simp [CFSG.LieType.Universal.Unitary.conjTr, Matrix.scalar, Matrix.diagonal, hij, hji]
  rw [hstar] at h
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) F => M 0 (Fin.rev 0)) h
  simpa [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, antidiag] using hentry

theorem isGLLift_commute_of_not_dvd_PSU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ 2 ^ f + 1)
    {c z : X} (hz : z ^ p = 1) (hcz : Commute c z) {s t : GL (Fin n) F}
    (hsJ : conjTr (unitaryInvolution F 2 f) (s : Matrix (Fin n) (Fin n) F) * antidiag n *
      (s : Matrix (Fin n) (Fin n) F) = antidiag n)
    (htJ : conjTr (unitaryInvolution F 2 f) (t : Matrix (Fin n) (Fin n) F) * antidiag n *
      (t : Matrix (Fin n) (Fin n) F) = antidiag n)
    (hs : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ s c)
    (ht : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ t z) :
    Commute s t := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    exact Units.ext (by ext i j; exact Fin.elim0 i)
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hst : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ (s * t) (z * c) :=
    ht.mul hs
  have hts : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ (t * s) (c * z) :=
    hs.mul ht
  rw [← hcz.eq] at hst
  obtain ⟨a, ha⟩ := isGLLift_unique_PSU hc n ψ hψ hst hts
  have htp : ∃ μ : F, ((t ^ p : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) μ := by
    have hlift : IsGLLift (Unitary.SU (unitaryInvolution F 2 f) n).subtype ψ (t ^ p) (1 : X) := by
      rw [← hz]
      exact ht.pow p
    obtain ⟨μ, hμ⟩ := isGLLift_unique_PSU hc n ψ hψ hlift
      (isGLLift_one (j := (Unitary.SU (unitaryInvolution F 2 f) n).subtype) (ψ := ψ))
    exact ⟨μ, by simpa using hμ⟩
  have hpa : a ^ p = 1 := pow_eq_one_of_commutator_eq_scalar ha htp
  have hζJ := isJUnitary_commutator hsJ htJ
  have hunit : conjTr (unitaryInvolution F 2 f) (Matrix.scalar (Fin n) a) * antidiag n *
      Matrix.scalar (Fin n) a = antidiag n := by
    rw [← ha]
    exact hζJ
  have hentry : unitaryInvolution F 2 f a * a = 1 :=
    scalar_mul_eq_one_of_isJUnitary hn hunit
  have hq : a ^ (2 ^ f + 1) = 1 := by
    rw [pow_succ, ← CFSG.LieType.BorelTits.unitaryInvolution_apply]
    exact hentry
  have hcop : Nat.Coprime p (2 ^ f + 1) := (hp.coprime_iff_not_dvd).mpr hpq
  have hdvd1 : orderOf a ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hpa
  have hdvd2 : orderOf a ∣ 2 ^ f + 1 := orderOf_dvd_iff_pow_eq_one.mpr hq
  have hgcd : orderOf a ∣ p.gcd (2 ^ f + 1) := Nat.dvd_gcd hdvd1 hdvd2
  have hcop' : p.gcd (2 ^ f + 1) = 1 := hcop
  rw [hcop'] at hgcd
  have ha1 : a = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  have hunit1 : ((t * s)⁻¹ * (s * t) : GL (Fin n) F) = 1 := by
    apply Units.ext
    rw [ha, ha1, map_one, Units.val_one]
  exact (inv_mul_eq_one.mp hunit1).symm

end CFSG.StandardType

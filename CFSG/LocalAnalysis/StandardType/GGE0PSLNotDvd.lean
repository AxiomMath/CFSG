module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSL
public import CFSG.LocalAnalysis.StandardType.GGE0LiftGeneric

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition

theorem isGLLift_commute_of_not_dvd_PSL (m : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    {X : Type} [Group X] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1)
    {c z : X} (hz : z ^ p = 1) (hcz : Commute c z) {s t : GL (Fin (m + 1)) F}
    (hs : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s c)
    (ht : IsGLLift Matrix.SpecialLinearGroup.toGL ψ t z) : Commute s t := by
  have hst : IsGLLift Matrix.SpecialLinearGroup.toGL ψ (s * t) (z * c) := ht.mul hs
  have hts : IsGLLift Matrix.SpecialLinearGroup.toGL ψ (t * s) (c * z) := hs.mul ht
  rw [← hcz.eq] at hst
  obtain ⟨a, ha⟩ := isGLLift_unique_PSL m F ψ hψ hst hts
  have htp : ∃ μ : F, ((t ^ p : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.scalar (Fin (m + 1)) μ := by
    have hlift : IsGLLift Matrix.SpecialLinearGroup.toGL ψ (t ^ p) (1 : X) := by
      rw [← hz]
      exact ht.pow p
    obtain ⟨μ, hμ⟩ := isGLLift_unique_PSL m F ψ hψ hlift
      (isGLLift_one (j := Matrix.SpecialLinearGroup.toGL) (ψ := ψ))
    exact ⟨μ, by simpa using hμ⟩
  have hpa : a ^ p = 1 := pow_eq_one_of_commutator_eq_scalar ha htp
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.pos.ne'] at hpa
    exact zero_ne_one hpa
  have hq : a ^ (Nat.card F - 1) = 1 := by
    have : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one a ha0
  have hcop : Nat.Coprime p (Nat.card F - 1) := (hp.coprime_iff_not_dvd).mpr hpq
  have hdvd1 : orderOf a ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hpa
  have hdvd2 : orderOf a ∣ Nat.card F - 1 := orderOf_dvd_iff_pow_eq_one.mpr hq
  have hgcd : orderOf a ∣ p.gcd (Nat.card F - 1) := Nat.dvd_gcd hdvd1 hdvd2
  have hcop' : p.gcd (Nat.card F - 1) = 1 := hcop
  rw [hcop'] at hgcd
  have ha1 : a = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  have hunit : ((t * s)⁻¹ * (s * t) : GL (Fin (m + 1)) F) = 1 := by
    apply Units.ext
    rw [ha, ha1, map_one, Units.val_one]
  exact (inv_mul_eq_one.mp hunit).symm

end CFSG.StandardType

module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95Y

public section

namespace CFSG.Quasithin.Fan86

namespace Sec9P4F95Alg

variable {H : Type*} [Group H] {x w za c : H} {y z : Fin 5 → H}

theorem yy_sq (hR : P1Rel x w za y z) {p q : Fin 5} (hpq : p ≠ q) :
    (y p * y q) * (y p * y q) = z (kstar p q) * z (kstar q p) := by
  have h := hR.yy p q hpq
  unfold fcomm at h
  rw [hR.y_inv, hR.y_inv] at h
  simpa only [mul_assoc] using h

theorem sq_pair (hR : P1Rel x w za y z) {p q : Fin 5} (hpq : p ≠ q) (a₀ a₁ a₂ a₃ b : ℕ) :
    (y p * y q * Ee z za a₀ a₁ a₂ a₃ b) * (y p * y q * Ee z za a₀ a₁ a₂ a₃ b) =
      z (kstar p q) * z (kstar q p) *
        za ^ (conjExp p a₀ a₁ a₂ a₃ + conjExp q a₀ a₁ a₂ a₃) := by
  have hconj : (y p * y q)⁻¹ * Ee z za a₀ a₁ a₂ a₃ b * (y p * y q) =
      Ee z za a₀ a₁ a₂ a₃ (b + (conjExp p a₀ a₁ a₂ a₃ + conjExp q a₀ a₁ a₂ a₃)) := by
    calc (y p * y q)⁻¹ * Ee z za a₀ a₁ a₂ a₃ b * (y p * y q)
        = (y q)⁻¹ * ((y p)⁻¹ * Ee z za a₀ a₁ a₂ a₃ b * y p) * y q := by group
      _ = _ := by
        rw [y_conj_Ee hR p, y_conj_Ee hR q]
        exact Ee_congr rfl rfl rfl rfl (by omega)
  have hEu : Ee z za a₀ a₁ a₂ a₃ b * (y p * y q) = (y p * y q) *
      Ee z za a₀ a₁ a₂ a₃ (b + (conjExp p a₀ a₁ a₂ a₃ + conjExp q a₀ a₁ a₂ a₃)) := by
    rw [← hconj]
    group
  calc (y p * y q * Ee z za a₀ a₁ a₂ a₃ b) * (y p * y q * Ee z za a₀ a₁ a₂ a₃ b)
      = (y p * y q) * (Ee z za a₀ a₁ a₂ a₃ b * (y p * y q)) * Ee z za a₀ a₁ a₂ a₃ b := by
        group
    _ = ((y p * y q) * (y p * y q)) * (Ee z za a₀ a₁ a₂ a₃
        (b + (conjExp p a₀ a₁ a₂ a₃ + conjExp q a₀ a₁ a₂ a₃)) * Ee z za a₀ a₁ a₂ a₃ b) := by
        rw [hEu]
        group
    _ = z (kstar p q) * z (kstar q p) *
        za ^ (conjExp p a₀ a₁ a₂ a₃ + conjExp q a₀ a₁ a₂ a₃) := by
        rw [yy_sq hR hpq, Ee_mul hR, show b + (conjExp p a₀ a₁ a₂ a₃ + conjExp q a₀ a₁ a₂ a₃) + b =
          b + (conjExp p a₀ a₁ a₂ a₃ + conjExp q a₀ a₁ a₂ a₃) + b from rfl, Ee_dbl hR]

theorem sq_pair_c (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) {p q : Fin 5} (hpq : p ≠ q)
    (hK : c * (y p * y q) = (y p * y q) * (z p * z q * za) * c) (a₀ a₁ a₂ a₃ b : ℕ) :
    (y p * y q * Ee z za a₀ a₁ a₂ a₃ b * c) * (y p * y q * Ee z za a₀ a₁ a₂ a₃ b * c) =
      z (kstar p q) * z (kstar q p) * z p * z q *
        za ^ (conjExp p a₀ a₁ a₂ a₃ + conjExp q a₀ a₁ a₂ a₃) := by
  have hcE : c * Ee z za a₀ a₁ a₂ a₃ b = Ee z za a₀ a₁ a₂ a₃ b * c :=
    (c_commute_Ee hC a₀ a₁ a₂ a₃ b).eq
  have hzE : (z p * z q * za) * Ee z za a₀ a₁ a₂ a₃ b =
      Ee z za a₀ a₁ a₂ a₃ b * (z p * z q * za) :=
    (((z_commute_Ee hR p a₀ a₁ a₂ a₃ b).mul_left (z_commute_Ee hR q a₀ a₁ a₂ a₃ b)).mul_left
      (za_commute_Ee hR a₀ a₁ a₂ a₃ b)).eq
  have hct : c * (y p * y q * Ee z za a₀ a₁ a₂ a₃ b) =
      (y p * y q * Ee z za a₀ a₁ a₂ a₃ b) * (z p * z q * za) * c := by
    calc c * (y p * y q * Ee z za a₀ a₁ a₂ a₃ b)
        = (c * (y p * y q)) * Ee z za a₀ a₁ a₂ a₃ b := by group
      _ = (y p * y q) * (z p * z q * za) * (c * Ee z za a₀ a₁ a₂ a₃ b) := by rw [hK]; group
      _ = (y p * y q) * ((z p * z q * za) * Ee z za a₀ a₁ a₂ a₃ b) * c := by rw [hcE]; group
      _ = (y p * y q) * (Ee z za a₀ a₁ a₂ a₃ b * (z p * z q * za)) * c := by rw [hzE]
      _ = _ := by group
  have hcc : c * c = za := by rw [← pow_two]; exact hC.c2
  have hzz : (z p * z q * za) * za = z p * z q := by
    rw [mul_assoc, ← pow_two, hR.za2, mul_one]
  have hn : za ^ (conjExp p a₀ a₁ a₂ a₃ + conjExp q a₀ a₁ a₂ a₃) * (z p * z q) =
      (z p * z q) * za ^ (conjExp p a₀ a₁ a₂ a₃ + conjExp q a₀ a₁ a₂ a₃) :=
    (((z_commute_za hR p).symm.pow_left _).mul_right ((z_commute_za hR q).symm.pow_left _)).eq
  calc (y p * y q * Ee z za a₀ a₁ a₂ a₃ b * c) * (y p * y q * Ee z za a₀ a₁ a₂ a₃ b * c)
      = (y p * y q * Ee z za a₀ a₁ a₂ a₃ b) * (c * (y p * y q * Ee z za a₀ a₁ a₂ a₃ b)) * c := by
        group
    _ = ((y p * y q * Ee z za a₀ a₁ a₂ a₃ b) * (y p * y q * Ee z za a₀ a₁ a₂ a₃ b)) *
        (z p * z q * za) * (c * c) := by rw [hct]; group
    _ = ((y p * y q * Ee z za a₀ a₁ a₂ a₃ b) * (y p * y q * Ee z za a₀ a₁ a₂ a₃ b)) *
        (z p * z q) := by rw [hcc, mul_assoc _ (z p * z q * za) za, hzz]
    _ = _ := by
        rw [sq_pair hR hpq, mul_assoc, hn]
        group

end Sec9P4F95Alg

end CFSG.Quasithin.Fan86

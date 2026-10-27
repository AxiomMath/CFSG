module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Kempf
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Quasithin.Background.F9Dihedral
public import CFSG.Quasithin.Background.G2A5

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits

theorem eq_mul_conj_of_inv {K : Type*} [Group K] {b s : K} (hb : b * b = 1) (hs : s ^ 3 = 1)
    (hbs : b * s * b = s⁻¹) : b * (s * b * s⁻¹) = s := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  have h1 : b * s = s⁻¹ * b := by
    calc b * s = b * s * b * b := by rw [mul_assoc (b * s), hb, mul_one]
      _ = s⁻¹ * b := by rw [hbs]
  calc b * (s * b * s⁻¹) = (b * s) * b * s⁻¹ := by group
    _ = s⁻¹ * (b * b) * s⁻¹ := by rw [h1]; group
    _ = s⁻¹ * s⁻¹ := by rw [hb, mul_one]
    _ = s⁻¹ * s⁻¹ * s ^ 3 := by rw [hs, mul_one]
    _ = s := by group

theorem mul_inv_of_inv {K : Type*} [Group K] {b s t : K} (hb : b * b = 1)
    (hbs : b * s * b = s⁻¹) (hbt : b * t * b = t⁻¹) (hst : s * t = t * s) :
    b * (s * t) * b = (s * t)⁻¹ := by
  calc b * (s * t) * b = b * s * (b * b) * t * b := by rw [hb, mul_one]; group
    _ = (b * s * b) * (b * t * b) := by group
    _ = (s * t)⁻¹ := by rw [hbs, hbt, ← mul_inv_rev, hst]

theorem mul_eq_of_inv {K : Type*} [Group K] {b s : K} (hb : b * b = 1) (hs : s ^ 3 = 1)
    (hbs : b * s * b = s⁻¹) : b * s = s * s * b := by
  have hsinv : s⁻¹ = s * s := by
    rw [inv_eq_iff_mul_eq_one, ← pow_three, hs]
  calc b * s = b * s * b * b := by rw [mul_assoc (b * s), hb, mul_one]
    _ = s * s * b := by rw [hbs, hsinv]

end CFSG.Quasithin.H13.A5

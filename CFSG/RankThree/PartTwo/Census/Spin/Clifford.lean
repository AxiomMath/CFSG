module

public import TauCeti.RepresentationTheory.Spin.Polarization.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

section Ring

variable {A : Type*} [Ring A]

theorem anticomm_symm {a b : A} (h : a * b = -(b * a)) : b * a = -(a * b) := by
  rw [h, neg_neg]

theorem bracket_of_anticomm {g₁ g₂ h h' : A} (h1 : g₁ * h = -(h * g₁)) (h2 : g₁ * g₂ = -(g₂ * g₁))
    (h3 : g₂ * h' = -(h' * g₂)) (hhh : h * h' + h' * h = 1) :
    g₁ * h' * (h * g₂) - h * g₂ * (g₁ * h') = g₁ * g₂ := by
  have h1' := anticomm_symm h1
  have h2' := anticomm_symm h2
  have e1 : h * g₂ * (g₁ * h') = -(g₁ * (h * h') * g₂) := by
    calc h * g₂ * (g₁ * h') = h * (g₂ * g₁) * h' := by noncomm_ring
      _ = -((h * g₁) * g₂ * h') := by rw [h2']; noncomm_ring
      _ = g₁ * h * (g₂ * h') := by rw [h1']; noncomm_ring
      _ = -(g₁ * (h * h') * g₂) := by rw [h3]; noncomm_ring
  rw [e1, sub_neg_eq_add]
  calc g₁ * h' * (h * g₂) + g₁ * (h * h') * g₂ = g₁ * (h * h' + h' * h) * g₂ := by noncomm_ring
    _ = g₁ * g₂ := by rw [hhh, mul_one]

theorem sandwich_eq_zero {g x : A} (hgx : g * x = -(x * g)) (hg : g * g = 0) : g * x * g = 0 := by
  rw [hgx, neg_mul, mul_assoc, hg, mul_zero, neg_zero]

theorem sandwich₂_eq_zero {g x y : A} (hgx : g * x = -(x * g)) (hgy : g * y = -(y * g))
    (hg : g * g = 0) : g * x * y * g = 0 := by
  rw [hgx, neg_mul, neg_mul, mul_assoc x g y, mul_assoc x, sandwich_eq_zero hgy hg, mul_zero,
    neg_zero]

theorem sandwich₃_eq_zero {g x y z : A} (hgx : g * x = -(x * g)) (hgy : g * y = -(y * g))
    (hgz : g * z = -(z * g)) (hg : g * g = 0) : g * x * y * z * g = 0 := by
  have e : g * x * y * z * g = -(x * (g * y * z * g)) := by
    rw [hgx]; noncomm_ring
  rw [e, sandwich₂_eq_zero hgy hgz hg, mul_zero, neg_zero]

theorem commute_of_anticomm {a b c d : A} (hac : a * c = -(c * a)) (had : a * d = -(d * a))
    (hbc : b * c = -(c * b)) (hbd : b * d = -(d * b)) : Commute (a * b) (c * d) := by
  show a * b * (c * d) = c * d * (a * b)
  calc a * b * (c * d) = a * (b * c) * d := by noncomm_ring
    _ = -(a * (c * b) * d) := by rw [hbc]; noncomm_ring
    _ = -((a * c) * (b * d)) := by noncomm_ring
    _ = -(-(c * a) * -(d * b)) := by rw [hac, hbd]
    _ = -(c * (a * d) * b) := by noncomm_ring
    _ = c * (d * a) * b := by rw [had]; noncomm_ring
    _ = c * d * (a * b) := by noncomm_ring

end Ring

namespace Cliff

open TauCeti CliffordAlgebra

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {P : SpinPolarizationData Q} {ι : Type*}
  (b : Module.Basis ι K P.W)

noncomputable abbrev cr (i : ι) : CliffordAlgebra Q := CliffordAlgebra.ι Q (b i : V)

noncomputable abbrev an (i : ι) : CliffordAlgebra Q :=
  CliffordAlgebra.ι Q (P.dualVector b i : V)

theorem isOrtho_of_polar {x y : V} (h : QuadraticMap.polar Q x y = 0) : Q.IsOrtho x y := by
  rw [← QuadraticMap.isOrtho_polarBilin, QuadraticMap.polarBilin_apply_apply]
  exact h

theorem cr_sq (i : ι) : cr b i * cr b i = 0 := by
  rw [cr, ι_sq_scalar, P.isotropic_W, map_zero]

theorem an_sq (i : ι) : an b i * an b i = 0 := by
  rw [an, ι_sq_scalar, P.isotropic_W', map_zero]

theorem cr_cr (i j : ι) : cr b i * cr b j = -(cr b j * cr b i) :=
  ι_mul_ι_comm_of_isOrtho (isOrtho_of_polar (P.polar_W_eq_zero (b i) (b j)))

theorem an_an (i j : ι) : an b i * an b j = -(an b j * an b i) :=
  ι_mul_ι_comm_of_isOrtho (isOrtho_of_polar (P.polar_W'_eq_zero _ _))

theorem cr_an {i j : ι} (hij : i ≠ j) : cr b i * an b j = -(an b j * cr b i) :=
  ι_mul_ι_comm_of_isOrtho (P.isOrtho_basis_dualVector b hij)

theorem an_cr {i j : ι} (hij : i ≠ j) : an b j * cr b i = -(cr b i * an b j) :=
  anticomm_symm (cr_an b hij)

theorem cr_an_self (i : ι) : cr b i * an b i + an b i * cr b i = 1 := by
  rw [cr, an, ι_mul_ι_add_swap, P.polar_dualVector_self, map_one]

theorem an_cr_self (i : ι) : an b i * cr b i + cr b i * an b i = 1 := by
  rw [add_comm, cr_an_self]

variable {i j k : ι}

theorem bracket_M_P (hjk : j ≠ k) :
    cr b i * an b j * (cr b j * cr b k) - cr b j * cr b k * (cr b i * an b j) =
      cr b i * cr b k :=
  bracket_of_anticomm (cr_cr b i j) (cr_cr b i k) (cr_an b hjk.symm) (cr_an_self b j)

theorem M_P_M (hij : i ≠ j) :
    cr b i * an b j * (cr b j * cr b k) * (cr b i * an b j) = 0 := by
  have e : cr b i * an b j * (cr b j * cr b k) * (cr b i * an b j) =
      cr b i * an b j * cr b j * cr b k * cr b i * an b j := by noncomm_ring
  rw [e, sandwich₃_eq_zero (cr_an b hij) (cr_cr b i j) (cr_cr b i k) (cr_sq b i),
    zero_mul]

theorem P_M_P (hjk : j ≠ k) :
    cr b j * cr b k * (cr b i * an b j) * (cr b j * cr b k) = 0 := by
  have e : cr b j * cr b k * (cr b i * an b j) * (cr b j * cr b k) =
      cr b j * (cr b k * cr b i * an b j * cr b j * cr b k) := by noncomm_ring
  rw [e, sandwich₃_eq_zero (cr_cr b k i) (cr_an b hjk.symm) (cr_cr b k j) (cr_sq b k),
    mul_zero]

theorem bracket_N_M (hjk : j ≠ k) :
    an b k * an b j * (cr b j * an b i) - cr b j * an b i * (an b k * an b j) =
      an b k * an b i :=
  bracket_of_anticomm (an_cr b hjk) (an_an b k i) (an_an b i j) (cr_an_self b j)

theorem N_M_N (hjk : j ≠ k) :
    an b k * an b j * (cr b j * an b i) * (an b k * an b j) = 0 := by
  have e : an b k * an b j * (cr b j * an b i) * (an b k * an b j) =
      an b k * an b j * cr b j * an b i * an b k * an b j := by noncomm_ring
  rw [e, sandwich₃_eq_zero (an_an b k j) (an_cr b hjk) (an_an b k i) (an_sq b k),
    zero_mul]

theorem M_N_M (hij : i ≠ j) :
    cr b j * an b i * (an b k * an b j) * (cr b j * an b i) = 0 := by
  have e : cr b j * an b i * (an b k * an b j) * (cr b j * an b i) =
      cr b j * (an b i * an b k * an b j * cr b j * an b i) := by noncomm_ring
  rw [e, sandwich₃_eq_zero (an_an b i k) (an_an b i j) (an_cr b hij.symm) (an_sq b i),
    mul_zero]

theorem cr_an_cr (i : ι) : cr b i * an b i * cr b i = cr b i := by
  have h : an b i * cr b i = 1 - cr b i * an b i := eq_sub_of_add_eq' (cr_an_self b i)
  rw [mul_assoc, h, mul_sub, mul_one, ← mul_assoc, cr_sq, zero_mul, sub_zero]

theorem an_cr_an (i : ι) : an b i * cr b i * an b i = an b i := by
  have h : cr b i * an b i = 1 - an b i * cr b i := eq_sub_of_add_eq' (an_cr_self b i)
  rw [mul_assoc, h, mul_sub, mul_one, ← mul_assoc, an_sq, zero_mul, sub_zero]

theorem P_N_P (hik : i ≠ k) :
    cr b i * cr b k * (an b k * an b i) * (cr b i * cr b k) = cr b i * cr b k := by
  have h1 : an b i * cr b i = 1 - cr b i * an b i := eq_sub_of_add_eq' (cr_an_self b i)
  have h3 : cr b i * cr b k * an b k * cr b i = 0 :=
    sandwich₂_eq_zero (cr_cr b i k) (cr_an b hik) (cr_sq b i)
  calc cr b i * cr b k * (an b k * an b i) * (cr b i * cr b k)
      = cr b i * cr b k * an b k * (an b i * cr b i) * cr b k := by noncomm_ring
    _ = cr b i * (cr b k * an b k * cr b k) -
          cr b i * cr b k * an b k * cr b i * an b i * cr b k := by rw [h1]; noncomm_ring
    _ = cr b i * cr b k := by rw [cr_an_cr, h3, zero_mul, zero_mul, sub_zero]

theorem N_P_N (hik : i ≠ k) :
    an b k * an b i * (cr b i * cr b k) * (an b k * an b i) = an b k * an b i := by
  have h1 : an b i * cr b i = 1 - cr b i * an b i := eq_sub_of_add_eq' (cr_an_self b i)
  have h3 : an b i * cr b k * an b k * an b i = 0 :=
    sandwich₂_eq_zero (an_cr b hik.symm) (an_an b i k) (an_sq b i)
  calc an b k * an b i * (cr b i * cr b k) * (an b k * an b i)
      = an b k * (an b i * cr b i) * cr b k * an b k * an b i := by noncomm_ring
    _ = an b k * cr b k * an b k * an b i -
          an b k * cr b i * (an b i * cr b k * an b k * an b i) := by rw [h1]; noncomm_ring
    _ = an b k * an b i := by rw [an_cr_an, h3, mul_zero, sub_zero]

theorem P_E : cr b i * cr b k * (cr b i * an b k) = 0 := by
  rw [← mul_assoc, sandwich_eq_zero (cr_cr b i k) (cr_sq b i), zero_mul]

theorem E_P (hik : i ≠ k) : cr b i * an b k * (cr b i * cr b k) = 0 := by
  rw [← mul_assoc, sandwich_eq_zero (cr_an b hik) (cr_sq b i), zero_mul]

theorem P_F : cr b i * cr b k * (cr b k * an b i) = 0 := by
  rw [mul_assoc, ← mul_assoc (cr b k), cr_sq, zero_mul, mul_zero]

theorem F_P (hik : i ≠ k) : cr b k * an b i * (cr b i * cr b k) = 0 := by
  rw [← mul_assoc]
  exact sandwich₂_eq_zero (cr_an b hik.symm) (cr_cr b k i) (cr_sq b k)

theorem N_E (hik : i ≠ k) : an b k * an b i * (cr b i * an b k) = 0 := by
  rw [← mul_assoc]
  exact sandwich₂_eq_zero (an_an b k i) (an_cr b hik) (an_sq b k)

theorem E_N : cr b i * an b k * (an b k * an b i) = 0 := by
  rw [mul_assoc, ← mul_assoc (an b k), an_sq, zero_mul, mul_zero]

theorem N_F (hik : i ≠ k) : an b k * an b i * (cr b k * an b i) = 0 := by
  rw [mul_assoc, ← mul_assoc (an b i), sandwich_eq_zero (an_cr b hik.symm) (an_sq b i),
    mul_zero]

theorem F_N : cr b k * an b i * (an b k * an b i) = 0 := by
  rw [mul_assoc, ← mul_assoc (an b i), sandwich_eq_zero (an_an b i k) (an_sq b i), mul_zero]

end Cliff

end CFSG.RankThree.PartTwo.Census.Spin

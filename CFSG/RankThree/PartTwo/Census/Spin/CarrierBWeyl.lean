module

public import CFSG.RankThree.PartTwo.Census.Spin.CarrierBTheta
public import CFSG.RankThree.PartTwo.Census.Spin.RootOpIn

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

namespace CarrierB

open TauCeti TauCeti.TypeBSpinCarrier Cliff

variable {n : ℕ}

section Long

variable {i k : Fin (n + 1)} (hik : i ≠ k)
include hik

noncomputable abbrev weylL (i k : Fin (n + 1)) : Cl n :=
  (1 + crB n i * anB n k) * (1 - crB n k * anB n i) * (1 + crB n i * anB n k)

theorem EL_sq : crB n i * anB n k * (crB n i * anB n k) = 0 := by
  rw [← mul_assoc, sandwich_eq_zero (cr_an (polarizationBasis n) hik)
    (cr_sq (polarizationBasis n) i), zero_mul]

theorem FL_sq : crB n k * anB n i * (crB n k * anB n i) = 0 := by
  rw [← mul_assoc, sandwich_eq_zero (cr_an (polarizationBasis n) hik.symm)
    (cr_sq (polarizationBasis n) k), zero_mul]

theorem weylL_mul_cr : weylL i k * crB n k = crB n i * weylL i k := by
  show (1 + crB n i * anB n k) * (1 - crB n k * anB n i) * (1 + crB n i * anB n k) * crB n k =
    crB n i * ((1 + crB n i * anB n k) * (1 - crB n k * anB n i) * (1 + crB n i * anB n k))
  set E := crB n i * anB n k with hEd
  set F := crB n k * anB n i with hFd
  have hE : E * E = 0 := EL_sq hik
  have hF : F * F = 0 := FL_sq hik
  have hki : anB n i * crB n k = -(crB n k * anB n i) := an_cr (polarizationBasis n) hik.symm
  have hik' : anB n k * crB n i = -(crB n i * anB n k) := an_cr (polarizationBasis n) hik
  have e1 : E * crB n k - crB n k * E = crB n i := by
    calc E * crB n k - crB n k * E
        = crB n i * (anB n k * crB n k) - crB n k * crB n i * anB n k := by
          rw [hEd]; noncomm_ring
      _ = crB n i * (anB n k * crB n k + crB n k * anB n k) := by
          rw [cr_cr (polarizationBasis n) k i]; noncomm_ring
      _ = crB n i := by rw [an_cr_self, mul_one]
  have e2 : E * crB n k * E = 0 := by
    have hc := commute_mul_of_anticomm₂ (cr_an (polarizationBasis n) hik)
      (cr_cr (polarizationBasis n) i k)
    calc E * crB n k * E = crB n i * (anB n k * crB n k) * crB n i * anB n k := by
          rw [hEd]; noncomm_ring
      _ = anB n k * crB n k * (crB n i * crB n i) * anB n k := by rw [hc]; noncomm_ring
      _ = 0 := by rw [cr_sq]; noncomm_ring
  have e3 : F * crB n k = 0 := by
    calc F * crB n k = crB n k * (anB n i * crB n k) := by rw [hFd]; noncomm_ring
      _ = 0 := by rw [hki, mul_neg, ← mul_assoc, cr_sq, zero_mul, neg_zero]
  have e4 : F * crB n i - crB n i * F = crB n k := by
    calc F * crB n i - crB n i * F
        = crB n k * (anB n i * crB n i) - crB n i * crB n k * anB n i := by
          rw [hFd]; noncomm_ring
      _ = crB n k * (anB n i * crB n i + crB n i * anB n i) := by
          rw [cr_cr (polarizationBasis n) i k]; noncomm_ring
      _ = crB n k := by rw [an_cr_self, mul_one]
  have e5 : F * crB n i * F = 0 := by
    have hc := commute_mul_of_anticomm₂ (cr_an (polarizationBasis n) hik.symm)
      (cr_cr (polarizationBasis n) k i)
    calc F * crB n i * F = crB n k * (anB n i * crB n i) * crB n k * anB n i := by
          rw [hFd]; noncomm_ring
      _ = anB n i * crB n i * (crB n k * crB n k) * anB n i := by rw [hc]; noncomm_ring
      _ = 0 := by rw [cr_sq]; noncomm_ring
  have e6 : E * crB n i = 0 := by
    calc E * crB n i = crB n i * (anB n k * crB n i) := by rw [hEd]; noncomm_ring
      _ = 0 := by rw [hik', mul_neg, ← mul_assoc, cr_sq, zero_mul, neg_zero]
  have e8 : crB n k * F = 0 := by rw [hFd, ← mul_assoc, cr_sq, zero_mul]
  have e9 : crB n i * E = 0 := by rw [hEd, ← mul_assoc, cr_sq, zero_mul]
  have s1 : (1 + E) * crB n k = (crB n k + crB n i) * (1 + E) := by
    rw [one_add_mul_eq hE, e1, e2, sub_zero]
  have s2 : (1 - F) * (crB n k + crB n i) = crB n i * (1 - F) := by
    rw [one_sub_mul_eq hF]
    have hFY : F * (crB n k + crB n i) - (crB n k + crB n i) * F = crB n k := by
      rw [mul_add, add_mul, e3, e8, zero_add, zero_add]
      exact e4
    have hFYF : F * (crB n k + crB n i) * F = 0 := by
      rw [mul_add, add_mul, e3, zero_mul, zero_add, e5]
    rw [hFY, hFYF, sub_zero, add_sub_cancel_left]
  have s3 : (1 + E) * crB n i = crB n i * (1 + E) := by
    rw [one_add_mul_eq hE, e6, e9, zero_mul, sub_zero, sub_zero, add_zero]
  calc (1 + E) * (1 - F) * (1 + E) * crB n k = (1 + E) * (1 - F) * ((1 + E) * crB n k) := by
        rw [mul_assoc]
    _ = (1 + E) * ((1 - F) * (crB n k + crB n i)) * (1 + E) := by rw [s1]; noncomm_ring
    _ = (1 + E) * crB n i * (1 - F) * (1 + E) := by rw [s2]; noncomm_ring
    _ = crB n i * ((1 + E) * (1 - F) * (1 + E)) := by rw [s3]; noncomm_ring

theorem weylL_mul_an : weylL i k * anB n k = anB n i * weylL i k := by
  show (1 + crB n i * anB n k) * (1 - crB n k * anB n i) * (1 + crB n i * anB n k) * anB n k =
    anB n i * ((1 + crB n i * anB n k) * (1 - crB n k * anB n i) * (1 + crB n i * anB n k))
  set E := crB n i * anB n k with hEd
  set F := crB n k * anB n i with hFd
  have hE : E * E = 0 := EL_sq hik
  have hF : F * F = 0 := FL_sq hik
  have g1 : E * anB n k = 0 := by rw [hEd, mul_assoc, an_sq, mul_zero]
  have g2 : anB n k * E = 0 := by
    calc anB n k * E = anB n k * crB n i * anB n k := by rw [hEd]; noncomm_ring
      _ = 0 := by
          rw [an_cr (polarizationBasis n) hik, neg_mul, mul_assoc, an_sq, mul_zero, neg_zero]
  have g3 : F * anB n k - anB n k * F = -anB n i := by
    calc F * anB n k - anB n k * F
        = crB n k * (anB n i * anB n k) - anB n k * crB n k * anB n i := by
          rw [hFd]; noncomm_ring
      _ = -((crB n k * anB n k + anB n k * crB n k) * anB n i) := by
          rw [an_an (polarizationBasis n) i k]; noncomm_ring
      _ = -anB n i := by rw [cr_an_self, one_mul]
  have g4 : F * anB n k * F = 0 := by
    have hc := commute_mul_of_anticomm₂ (an_an (polarizationBasis n) i k)
      (an_cr (polarizationBasis n) hik.symm)
    calc F * anB n k * F = crB n k * (anB n i * (anB n k * crB n k)) * anB n i := by
          rw [hFd]; noncomm_ring
      _ = crB n k * (anB n k * crB n k) * (anB n i * anB n i) := by rw [hc]; noncomm_ring
      _ = 0 := by rw [an_sq]; noncomm_ring
  have g5 : E * anB n i - anB n i * E = -anB n k := by
    calc E * anB n i - anB n i * E
        = crB n i * (anB n k * anB n i) - anB n i * crB n i * anB n k := by
          rw [hEd]; noncomm_ring
      _ = -((crB n i * anB n i + anB n i * crB n i) * anB n k) := by
          rw [an_an (polarizationBasis n) k i]; noncomm_ring
      _ = -anB n k := by rw [cr_an_self, one_mul]
  have g6 : E * anB n i * E = 0 := by
    have hc := commute_mul_of_anticomm₂ (an_an (polarizationBasis n) k i)
      (an_cr (polarizationBasis n) hik)
    calc E * anB n i * E = crB n i * (anB n k * (anB n i * crB n i)) * anB n k := by
          rw [hEd]; noncomm_ring
      _ = crB n i * (anB n i * crB n i) * (anB n k * anB n k) := by rw [hc]; noncomm_ring
      _ = 0 := by rw [an_sq]; noncomm_ring
  have s1 : (1 + E) * anB n k = anB n k * (1 + E) := by
    rw [one_add_mul_eq hE, g1, g2, sub_zero, zero_mul, sub_zero, add_zero]
  have s2 : (1 - F) * anB n k = (anB n k + anB n i) * (1 - F) := by
    rw [one_sub_mul_eq hF, g3, g4, sub_zero, sub_neg_eq_add]
  have s3 : (1 + E) * (anB n k + anB n i) = anB n i * (1 + E) := by
    rw [one_add_mul_eq hE]
    have hEY : E * (anB n k + anB n i) - (anB n k + anB n i) * E = -anB n k := by
      rw [mul_add, add_mul, g1, g2, zero_add, zero_add]
      exact g5
    have hEYE : E * (anB n k + anB n i) * E = 0 := by
      rw [mul_add, add_mul, g1, zero_mul, zero_add, g6]
    rw [hEY, hEYE, sub_zero, ← sub_eq_add_neg, add_sub_cancel_left]
  calc (1 + E) * (1 - F) * (1 + E) * anB n k = (1 + E) * (1 - F) * ((1 + E) * anB n k) := by
        rw [mul_assoc]
    _ = (1 + E) * ((1 - F) * anB n k) * (1 + E) := by rw [s1]; noncomm_ring
    _ = (1 + E) * (anB n k + anB n i) * (1 - F) * (1 + E) := by rw [s2]; noncomm_ring
    _ = anB n i * ((1 + E) * (1 - F) * (1 + E)) := by rw [s3]; noncomm_ring

omit hik in
theorem commute_weylL {g : Cl n} (h1 : g * crB n i = -(crB n i * g))
    (h2 : g * anB n i = -(anB n i * g)) (h3 : g * crB n k = -(crB n k * g))
    (h4 : g * anB n k = -(anB n k * g)) : Commute g (weylL i k) :=
  commute_weyl_of (commute_mul_of_anticomm₂ h1 h4) (commute_mul_of_anticomm₂ h3 h2)

end Long

section Short

variable (n)

noncomputable abbrev weylS : Cl n :=
  (1 + crB n (Fin.last n) * zeta n) * (1 - zeta n * anB n (Fin.last n)) *
    (1 + crB n (Fin.last n) * zeta n)

theorem ES_sq : crB n (Fin.last n) * zeta n * (crB n (Fin.last n) * zeta n) = 0 := by
  calc crB n (Fin.last n) * zeta n * (crB n (Fin.last n) * zeta n)
      = crB n (Fin.last n) * (zeta n * crB n (Fin.last n)) * zeta n := by noncomm_ring
    _ = 0 := by
        rw [zeta_cr, mul_neg, ← mul_assoc, cr_sq (polarizationBasis n), zero_mul, neg_mul,
          zero_mul, neg_zero]

theorem FS_sq : zeta n * anB n (Fin.last n) * (zeta n * anB n (Fin.last n)) = 0 := by
  calc zeta n * anB n (Fin.last n) * (zeta n * anB n (Fin.last n))
      = zeta n * (anB n (Fin.last n) * zeta n) * anB n (Fin.last n) := by noncomm_ring
    _ = 0 := by
        rw [an_zeta, mul_neg, ← mul_assoc, zeta_sq, one_mul, neg_mul,
          an_sq (polarizationBasis n), neg_zero]

theorem weylS_mul_an : weylS n * anB n (Fin.last n) = -crB n (Fin.last n) * weylS n := by
  show (1 + crB n (Fin.last n) * zeta n) * (1 - zeta n * anB n (Fin.last n)) *
    (1 + crB n (Fin.last n) * zeta n) * anB n (Fin.last n) = -crB n (Fin.last n) *
    ((1 + crB n (Fin.last n) * zeta n) * (1 - zeta n * anB n (Fin.last n)) *
      (1 + crB n (Fin.last n) * zeta n))
  set c := crB n (Fin.last n) with hc
  set c' := anB n (Fin.last n) with hc'
  set z := zeta n with hz
  set E := c * z with hEd
  set F := z * c' with hFd
  have hE : E * E = 0 := ES_sq n
  have hF : F * F = 0 := FS_sq n
  have zz : z * z = 1 := zeta_sq n
  have zc : z * c = -(c * z) := zeta_cr n _
  have zc' : z * c' = -(c' * z) := zeta_an n _
  have cc : c * c = 0 := cr_sq (polarizationBasis n) _
  have cc' : c' * c' = 0 := an_sq (polarizationBasis n) _
  have hcc' : c * c' + c' * c = 1 := cr_an_self (polarizationBasis n) _
  have hcom : z * (c' * c) = c' * c * z := commute_mul_of_anticomm₂ zc' zc
  have cz : c * z = -(z * c) := by rw [zc, neg_neg]
  have cz' : c' * z = -(z * c') := by rw [zc', neg_neg]
  have h1 : E * c' - c' * E = -z := by
    calc E * c' - c' * E = c * (z * c') - c' * c * z := by rw [hEd]; noncomm_ring
      _ = -((c * c' + c' * c) * z) := by rw [zc']; noncomm_ring
      _ = -z := by rw [hcc', one_mul]
  have h2 : E * c' * E = c := by
    calc E * c' * E = c * (z * (c' * c) * z) := by rw [hEd]; noncomm_ring
      _ = c * c' * c * (z * z) := by rw [hcom]; noncomm_ring
      _ = c := by rw [zz, mul_one, cr_an_cr]
  have s1 : (1 + E) * c' = (c' - z - c) * (1 + E) := by
    rw [one_add_mul_eq hE, h1, h2, ← sub_eq_add_neg]
  have f1 : F * c' - c' * F = 0 := by
    calc F * c' - c' * F = z * (c' * c') - c' * z * c' := by rw [hFd]; noncomm_ring
      _ = z * (c' * c') + z * (c' * c') := by rw [cz']; noncomm_ring
      _ = 0 := by rw [cc', mul_zero, add_zero]
  have f2 : F * z - z * F = -(c' + c') := by
    calc F * z - z * F = z * (c' * z) - z * z * c' := by rw [hFd]; noncomm_ring
      _ = -(z * z * c') - z * z * c' := by rw [cz']; noncomm_ring
      _ = -(c' + c') := by rw [zz, one_mul]; abel
  have f3 : F * c - c * F = z := by
    calc F * c - c * F = z * (c' * c) - c * z * c' := by rw [hFd]; noncomm_ring
      _ = z * (c' * c + c * c') := by rw [cz]; noncomm_ring
      _ = z := by rw [add_comm (c' * c) (c * c'), hcc', mul_one]
  have f4 : F * c' * F = 0 := by
    calc F * c' * F = z * (c' * c') * z * c' := by rw [hFd]; noncomm_ring
      _ = 0 := by rw [cc']; noncomm_ring
  have f5 : F * z * F = 0 := by
    calc F * z * F = z * c' * (z * z) * c' := by rw [hFd]; noncomm_ring
      _ = 0 := by rw [zz, mul_one, mul_assoc, cc', mul_zero]
  have f6 : F * c * F = c' := by
    calc F * c * F = z * (c' * c) * z * c' := by rw [hFd]; noncomm_ring
      _ = c' * c * (z * z) * c' := by rw [hcom]; noncomm_ring
      _ = c' := by rw [zz, mul_one, an_cr_an]
  have s2 : (1 - F) * (c' - z - c) = -c * (1 - F) := by
    rw [one_sub_mul_eq hF]
    congr 1
    have e1 : F * (c' - z - c) - (c' - z - c) * F =
        (F * c' - c' * F) - (F * z - z * F) - (F * c - c * F) := by noncomm_ring
    have e2 : F * (c' - z - c) * F = F * c' * F - F * z * F - F * c * F := by noncomm_ring
    rw [e1, e2, f1, f2, f3, f4, f5, f6]
    abel
  have Ec : E * c = 0 := by
    calc E * c = c * (z * c) := by rw [hEd]; noncomm_ring
      _ = 0 := by rw [zc, mul_neg, ← mul_assoc, cc, zero_mul, neg_zero]
  have cE : c * E = 0 := by rw [hEd, ← mul_assoc, cc, zero_mul]
  have s3 : (1 + E) * (-c) = -c * (1 + E) := by
    have e1 : E * (-c) - (-c) * E = 0 := by rw [mul_neg, neg_mul, Ec, cE]; simp
    have e2 : E * (-c) * E = 0 := by rw [mul_neg, Ec]; simp
    rw [one_add_mul_eq hE, e1, e2, add_zero, sub_zero]
  calc (1 + E) * (1 - F) * (1 + E) * c' = (1 + E) * (1 - F) * ((1 + E) * c') := by
        rw [mul_assoc]
    _ = (1 + E) * ((1 - F) * (c' - z - c)) * (1 + E) := by rw [s1]; noncomm_ring
    _ = (1 + E) * (-c) * (1 - F) * (1 + E) := by rw [s2]; noncomm_ring
    _ = -c * ((1 + E) * (1 - F) * (1 + E)) := by rw [s3]; noncomm_ring

theorem weylS_mul_cr : weylS n * crB n (Fin.last n) = -anB n (Fin.last n) * weylS n := by
  show (1 + crB n (Fin.last n) * zeta n) * (1 - zeta n * anB n (Fin.last n)) *
    (1 + crB n (Fin.last n) * zeta n) * crB n (Fin.last n) = -anB n (Fin.last n) *
    ((1 + crB n (Fin.last n) * zeta n) * (1 - zeta n * anB n (Fin.last n)) *
      (1 + crB n (Fin.last n) * zeta n))
  set c := crB n (Fin.last n) with hc
  set c' := anB n (Fin.last n) with hc'
  set z := zeta n with hz
  set E := c * z with hEd
  set F := z * c' with hFd
  have hE : E * E = 0 := ES_sq n
  have hF : F * F = 0 := FS_sq n
  have zz : z * z = 1 := zeta_sq n
  have zc : z * c = -(c * z) := zeta_cr n _
  have zc' : z * c' = -(c' * z) := zeta_an n _
  have cc : c * c = 0 := cr_sq (polarizationBasis n) _
  have hcc' : c * c' + c' * c = 1 := cr_an_self (polarizationBasis n) _
  have hcom : z * (c' * c) = c' * c * z := commute_mul_of_anticomm₂ zc' zc
  have hcom' : z * (c * c') = c * c' * z := commute_mul_of_anticomm₂ zc zc'
  have cz : c * z = -(z * c) := by rw [zc, neg_neg]
  have Ec : E * c = 0 := by
    calc E * c = c * (z * c) := by rw [hEd]; noncomm_ring
      _ = 0 := by rw [zc, mul_neg, ← mul_assoc, cc, zero_mul, neg_zero]
  have cE : c * E = 0 := by rw [hEd, ← mul_assoc, cc, zero_mul]
  have s1 : (1 + E) * c = c * (1 + E) := by
    rw [one_add_mul_eq hE, Ec, cE, zero_mul, sub_zero, sub_zero, add_zero]
  have f3 : F * c - c * F = z := by
    calc F * c - c * F = z * (c' * c) - c * z * c' := by rw [hFd]; noncomm_ring
      _ = z * (c' * c + c * c') := by rw [cz]; noncomm_ring
      _ = z := by rw [add_comm (c' * c) (c * c'), hcc', mul_one]
  have f6 : F * c * F = c' := by
    calc F * c * F = z * (c' * c) * z * c' := by rw [hFd]; noncomm_ring
      _ = c' * c * (z * z) * c' := by rw [hcom]; noncomm_ring
      _ = c' := by rw [zz, mul_one, an_cr_an]
  have s2 : (1 - F) * c = (c - z - c') * (1 - F) := by
    rw [one_sub_mul_eq hF, f3, f6]
  have g1 : E * z - z * E = c + c := by
    calc E * z - z * E = c * (z * z) - z * c * z := by rw [hEd]; noncomm_ring
      _ = c * (z * z) + c * (z * z) := by rw [zc]; noncomm_ring
      _ = c + c := by rw [zz, mul_one]
  have g2 : E * c' - c' * E = -z := by
    calc E * c' - c' * E = c * (z * c') - c' * c * z := by rw [hEd]; noncomm_ring
      _ = -((c * c' + c' * c) * z) := by rw [zc']; noncomm_ring
      _ = -z := by rw [hcc', one_mul]
  have g3 : E * z * E = 0 := by
    calc E * z * E = c * (z * z) * c * z := by rw [hEd]; noncomm_ring
      _ = 0 := by rw [zz, mul_one, cc, zero_mul]
  have g4 : E * c' * E = c := by
    calc E * c' * E = c * (z * (c' * c) * z) := by rw [hEd]; noncomm_ring
      _ = c * c' * c * (z * z) := by rw [hcom]; noncomm_ring
      _ = c := by rw [zz, mul_one, cr_an_cr]
  have s3 : (1 + E) * (c - z - c') = -c' * (1 + E) := by
    rw [one_add_mul_eq hE]
    congr 1
    have e1 : E * (c - z - c') - (c - z - c') * E =
        (E * c - c * E) - (E * z - z * E) - (E * c' - c' * E) := by noncomm_ring
    have e2 : E * (c - z - c') * E = E * c * E - E * z * E - E * c' * E := by noncomm_ring
    rw [e1, e2, Ec, cE, g1, g2, g3, g4, zero_mul]
    abel
  calc (1 + E) * (1 - F) * (1 + E) * c = (1 + E) * (1 - F) * ((1 + E) * c) := by
        rw [mul_assoc]
    _ = (1 + E) * ((1 - F) * c) * (1 + E) := by rw [s1]; noncomm_ring
    _ = (1 + E) * (c - z - c') * (1 - F) * (1 + E) := by rw [s2]; noncomm_ring
    _ = -c' * ((1 + E) * (1 - F) * (1 + E)) := by rw [s3]; noncomm_ring

theorem commute_weylS {g : Cl n} (h1 : g * crB n (Fin.last n) = -(crB n (Fin.last n) * g))
    (h2 : g * anB n (Fin.last n) = -(anB n (Fin.last n) * g))
    (h3 : g * zeta n = -(zeta n * g)) : Commute g (weylS n) :=
  commute_weyl_of (commute_mul_of_anticomm₂ h1 h3) (commute_mul_of_anticomm₂ h3 h2)

end Short

section ShortRoots

variable (n)

theorem S_sq (i : Fin (n + 1)) : crB n i * zeta n * (crB n i * zeta n) = 0 := by
  calc crB n i * zeta n * (crB n i * zeta n) = crB n i * (zeta n * crB n i) * zeta n := by
        noncomm_ring
    _ = 0 := by
        rw [zeta_cr, mul_neg, ← mul_assoc, cr_sq (polarizationBasis n), zero_mul, neg_mul,
          zero_mul, neg_zero]

theorem T_sq (i : Fin (n + 1)) : zeta n * anB n i * (zeta n * anB n i) = 0 := by
  calc zeta n * anB n i * (zeta n * anB n i) = zeta n * (anB n i * zeta n) * anB n i := by
        noncomm_ring
    _ = 0 := by
        rw [an_zeta, mul_neg, ← mul_assoc, zeta_sq, one_mul, neg_mul,
          an_sq (polarizationBasis n), neg_zero]

theorem STS (i : Fin (n + 1)) :
    crB n i * zeta n * (zeta n * anB n i) * (crB n i * zeta n) = crB n i * zeta n := by
  calc crB n i * zeta n * (zeta n * anB n i) * (crB n i * zeta n)
      = crB n i * (zeta n * zeta n) * anB n i * crB n i * zeta n := by noncomm_ring
    _ = crB n i * zeta n := by rw [zeta_sq, mul_one, cr_an_cr]

theorem TST (i : Fin (n + 1)) :
    zeta n * anB n i * (crB n i * zeta n) * (zeta n * anB n i) = zeta n * anB n i := by
  calc zeta n * anB n i * (crB n i * zeta n) * (zeta n * anB n i)
      = zeta n * (anB n i * crB n i * (zeta n * zeta n) * anB n i) := by noncomm_ring
    _ = zeta n * anB n i := by rw [zeta_sq, mul_one, an_cr_an]

variable {n}

theorem SS_anticomm {i j : Fin (n + 1)} :
    crB n i * zeta n * (crB n j * zeta n) = -(crB n j * zeta n * (crB n i * zeta n)) := by
  calc crB n i * zeta n * (crB n j * zeta n) = crB n i * (zeta n * crB n j) * zeta n := by
        noncomm_ring
    _ = -(crB n i * crB n j * (zeta n * zeta n)) := by rw [zeta_cr]; noncomm_ring
    _ = -(-(crB n j * crB n i * (zeta n * zeta n))) := by
        rw [cr_cr (polarizationBasis n) i j]; noncomm_ring
    _ = -(crB n j * (zeta n * crB n i) * zeta n) := by rw [zeta_cr]; noncomm_ring
    _ = -(crB n j * zeta n * (crB n i * zeta n)) := by noncomm_ring

theorem ST_anticomm {i j : Fin (n + 1)} (hij : i ≠ j) :
    crB n i * zeta n * (zeta n * anB n j) = -(zeta n * anB n j * (crB n i * zeta n)) := by
  have hc := commute_mul_of_anticomm₂ (zeta_an n j) (zeta_cr n i)
  calc crB n i * zeta n * (zeta n * anB n j) = crB n i * (zeta n * zeta n) * anB n j := by
        noncomm_ring
    _ = -(anB n j * crB n i * (zeta n * zeta n)) := by
        rw [zeta_sq, mul_one, mul_one, cr_an (polarizationBasis n) hij]
    _ = -(zeta n * (anB n j * crB n i) * zeta n) := by
        rw [hc]; noncomm_ring
    _ = -(zeta n * anB n j * (crB n i * zeta n)) := by noncomm_ring

theorem TT_anticomm {i j : Fin (n + 1)} :
    zeta n * anB n i * (zeta n * anB n j) = -(zeta n * anB n j * (zeta n * anB n i)) := by
  calc zeta n * anB n i * (zeta n * anB n j) = zeta n * (anB n i * zeta n) * anB n j := by
        noncomm_ring
    _ = -((zeta n * zeta n) * (anB n i * anB n j)) := by rw [an_zeta]; noncomm_ring
    _ = -(-((zeta n * zeta n) * (anB n j * anB n i))) := by
        rw [an_an (polarizationBasis n) i j]; noncomm_ring
    _ = -(zeta n * (anB n j * zeta n) * anB n i) := by rw [an_zeta]; noncomm_ring
    _ = -(zeta n * anB n j * (zeta n * anB n i)) := by noncomm_ring

end ShortRoots

section Commutators

theorem zeta_conj_three {x y w : Cl n} (hx : zeta n * x = -(x * zeta n))
    (hy : zeta n * y = -(y * zeta n)) (hw : zeta n * w = -(w * zeta n)) :
    zeta n * (x * y * w) * zeta n = -(x * y * w) := by
  rw [mul_anticomm_three hx hy hw, neg_mul, mul_assoc (x * y * w), zeta_sq, mul_one]

variable {l m : Fin (n + 1)} (hlm : l ≠ m)
include hlm

theorem LSL_zero : crB n l * crB n m * (zeta n * anB n l) * (crB n l * crB n m) = 0 := by
  have h := sandwich₃_eq_zero (cr_zeta n m) (cr_an (polarizationBasis n) hlm.symm)
    (cr_cr (polarizationBasis n) m l) (cr_sq (polarizationBasis n) m)
  calc crB n l * crB n m * (zeta n * anB n l) * (crB n l * crB n m)
      = crB n l * (crB n m * zeta n * anB n l * crB n l * crB n m) := by noncomm_ring
    _ = 0 := by rw [h, mul_zero]

theorem LS_bracket : crB n l * crB n m * (zeta n * anB n l) -
    zeta n * anB n l * (crB n l * crB n m) = crB n m * zeta n := by
  have h1 : anB n l * (crB n m * zeta n) = crB n m * zeta n * anB n l :=
    commute_mul_of_anticomm₂ (an_cr (polarizationBasis n) hlm.symm) (an_zeta n l)
  have h2 : zeta n * (anB n l * crB n l) = anB n l * crB n l * zeta n :=
    commute_mul_of_anticomm₂ (zeta_an n l) (zeta_cr n l)
  calc crB n l * crB n m * (zeta n * anB n l) - zeta n * anB n l * (crB n l * crB n m)
      = crB n l * (crB n m * zeta n * anB n l) - zeta n * (anB n l * crB n l) * crB n m := by
        noncomm_ring
    _ = crB n l * anB n l * (crB n m * zeta n) - anB n l * crB n l * (zeta n * crB n m) := by
        rw [← h1, h2]; noncomm_ring
    _ = (crB n l * anB n l + anB n l * crB n l) * (crB n m * zeta n) := by
        rw [zeta_cr]; noncomm_ring
    _ = crB n m * zeta n := by rw [cr_an_self, one_mul]

theorem SLS_eq : zeta n * anB n l * (crB n l * crB n m) * (zeta n * anB n l) =
    -(crB n m * anB n l) := by
  have h := zeta_conj_three (zeta_an n l) (zeta_cr n l) (zeta_cr n m)
  calc zeta n * anB n l * (crB n l * crB n m) * (zeta n * anB n l)
      = zeta n * (anB n l * crB n l * crB n m) * zeta n * anB n l := by noncomm_ring
    _ = -(anB n l * crB n l * (crB n m * anB n l)) := by rw [h]; noncomm_ring
    _ = anB n l * crB n l * anB n l * crB n m := by
        rw [cr_an (polarizationBasis n) hlm.symm]; noncomm_ring
    _ = -(crB n m * anB n l) := by
        rw [an_cr_an, an_cr (polarizationBasis n) hlm.symm]

omit hlm in
theorem EF_zero : crB n m * zeta n * (crB n m * anB n l) = 0 := by
  calc crB n m * zeta n * (crB n m * anB n l) = crB n m * (zeta n * crB n m) * anB n l := by
        noncomm_ring
    _ = 0 := by
        rw [zeta_cr, mul_neg, ← mul_assoc, cr_sq (polarizationBasis n), zero_mul, neg_mul,
          zero_mul, neg_zero]

theorem LSL_zero' : anB n m * anB n l * (crB n l * zeta n) * (anB n m * anB n l) = 0 := by
  have h := sandwich₃_eq_zero (an_an (polarizationBasis n) m l)
    (an_cr (polarizationBasis n) hlm) (an_zeta n m) (an_sq (polarizationBasis n) m)
  calc anB n m * anB n l * (crB n l * zeta n) * (anB n m * anB n l)
      = anB n m * anB n l * crB n l * zeta n * anB n m * anB n l := by noncomm_ring
    _ = 0 := by rw [h, zero_mul]

theorem LS_bracket' : anB n m * anB n l * (crB n l * zeta n) -
    crB n l * zeta n * (anB n m * anB n l) = -(zeta n * anB n m) := by
  have h1 : anB n m * (anB n l * crB n l) = anB n l * crB n l * anB n m :=
    commute_mul_of_anticomm₂ (an_an (polarizationBasis n) m l) (an_cr (polarizationBasis n) hlm)
  have h2 : crB n l * (zeta n * anB n m) = zeta n * anB n m * crB n l :=
    commute_mul_of_anticomm₂ (cr_zeta n l) (cr_an (polarizationBasis n) hlm)
  have h3 : zeta n * anB n m * (crB n l * anB n l) = crB n l * anB n l * (zeta n * anB n m) := by
    have e1 : zeta n * (crB n l * anB n l) = crB n l * anB n l * zeta n :=
      commute_mul_of_anticomm₂ (zeta_cr n l) (zeta_an n l)
    have e2 : anB n m * (crB n l * anB n l) = crB n l * anB n l * anB n m :=
      commute_mul_of_anticomm₂ (an_cr (polarizationBasis n) hlm) (an_an (polarizationBasis n) m l)
    calc zeta n * anB n m * (crB n l * anB n l) = zeta n * (anB n m * (crB n l * anB n l)) := by
          noncomm_ring
      _ = zeta n * (crB n l * anB n l) * anB n m := by rw [e2]; noncomm_ring
      _ = crB n l * anB n l * (zeta n * anB n m) := by rw [e1]; noncomm_ring
  calc anB n m * anB n l * (crB n l * zeta n) - crB n l * zeta n * (anB n m * anB n l)
      = anB n m * (anB n l * crB n l) * zeta n - crB n l * (zeta n * anB n m) * anB n l := by
        noncomm_ring
    _ = anB n l * crB n l * (anB n m * zeta n) - zeta n * anB n m * (crB n l * anB n l) := by
        rw [h1, h2]; noncomm_ring
    _ = -((anB n l * crB n l + crB n l * anB n l) * (zeta n * anB n m)) := by
        rw [h3, an_zeta]; noncomm_ring
    _ = -(zeta n * anB n m) := by rw [an_cr_self, one_mul]

theorem SLS_eq' : crB n l * zeta n * (anB n m * anB n l) * (crB n l * zeta n) =
    -(crB n l * anB n m) := by
  have h := zeta_conj_three (zeta_an n m) (zeta_an n l) (zeta_cr n l)
  calc crB n l * zeta n * (anB n m * anB n l) * (crB n l * zeta n)
      = crB n l * (zeta n * (anB n m * anB n l * crB n l) * zeta n) := by noncomm_ring
    _ = -(crB n l * anB n m * anB n l * crB n l) := by rw [h]; noncomm_ring
    _ = anB n m * (crB n l * anB n l * crB n l) := by
        rw [cr_an (polarizationBasis n) hlm]; noncomm_ring
    _ = -(crB n l * anB n m) := by
        rw [cr_an_cr, an_cr (polarizationBasis n) hlm]

theorem FE_zero : zeta n * anB n m * (crB n l * anB n m) = 0 := by
  calc zeta n * anB n m * (crB n l * anB n m) = zeta n * (anB n m * crB n l) * anB n m := by
        noncomm_ring
    _ = -(zeta n * crB n l * (anB n m * anB n m)) := by
        rw [an_cr (polarizationBasis n) hlm]; noncomm_ring
    _ = 0 := by rw [an_sq (polarizationBasis n), mul_zero, neg_zero]

end Commutators

end CarrierB

end CFSG.RankThree.PartTwo.Census.Spin

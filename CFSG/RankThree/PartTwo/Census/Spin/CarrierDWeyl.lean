module

public import CFSG.RankThree.PartTwo.Census.Spin.CarrierDTheta
public import CFSG.RankThree.PartTwo.Census.Spin.RootOpIn
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessTwo

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

namespace Cliff

open TauCeti CliffordAlgebra

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {P : SpinPolarizationData Q} {ι : Type*}
  (b : Module.Basis ι K P.W)

noncomputable abbrev chainWeyl (i k : ι) : CliffordAlgebra Q :=
  (1 + cr b i * an b k) * (1 - cr b k * an b i) * (1 + cr b i * an b k)

noncomputable abbrev pairWeyl (i k : ι) : CliffordAlgebra Q :=
  (1 + cr b i * cr b k) * (1 - an b k * an b i) * (1 + cr b i * cr b k)

noncomputable abbrev signWeyl (i k : ι) : CliffordAlgebra Q := chainWeyl b i k * pairWeyl b i k

variable {b} {i k : ι} (hik : i ≠ k)
include hik

theorem chain_E_sq : cr b i * an b k * (cr b i * an b k) = 0 := by
  rw [← mul_assoc, sandwich_eq_zero (cr_an b hik) (cr_sq b i), zero_mul]

theorem chain_F_sq : cr b k * an b i * (cr b k * an b i) = 0 := by
  rw [← mul_assoc, sandwich_eq_zero (cr_an b hik.symm) (cr_sq b k), zero_mul]

omit hik in
theorem pair_E_sq : cr b i * cr b k * (cr b i * cr b k) = 0 := by
  calc cr b i * cr b k * (cr b i * cr b k) = cr b i * (cr b k * cr b i) * cr b k := by
        noncomm_ring
    _ = 0 := by rw [cr_cr b k i, mul_neg, neg_mul, ← mul_assoc, cr_sq, zero_mul]; simp

omit hik in
theorem pair_F_sq : an b k * an b i * (an b k * an b i) = 0 := by
  calc an b k * an b i * (an b k * an b i) = an b k * (an b i * an b k) * an b i := by
        noncomm_ring
    _ = 0 := by rw [an_an b i k, mul_neg, neg_mul, ← mul_assoc, an_sq, zero_mul]; simp

theorem chainWeyl_mul_cr : chainWeyl b i k * cr b k = cr b i * chainWeyl b i k := by
  show (1 + cr b i * an b k) * (1 - cr b k * an b i) * (1 + cr b i * an b k) * cr b k =
    cr b i * ((1 + cr b i * an b k) * (1 - cr b k * an b i) * (1 + cr b i * an b k))
  set E := cr b i * an b k with hEd
  set F := cr b k * an b i with hFd
  have hE : E * E = 0 := chain_E_sq hik
  have hF : F * F = 0 := chain_F_sq hik
  have hki : an b i * cr b k = -(cr b k * an b i) := an_cr b hik.symm
  have hik' : an b k * cr b i = -(cr b i * an b k) := an_cr b hik
  have e1 : E * cr b k - cr b k * E = cr b i := by
    calc E * cr b k - cr b k * E
        = cr b i * (an b k * cr b k) - cr b k * cr b i * an b k := by
          rw [hEd]; noncomm_ring
      _ = cr b i * (an b k * cr b k + cr b k * an b k) := by
          rw [cr_cr b k i]; noncomm_ring
      _ = cr b i := by rw [an_cr_self, mul_one]
  have e2 : E * cr b k * E = 0 := by
    have hc := commute_mul_of_anticomm₂ (cr_an b hik) (cr_cr b i k)
    calc E * cr b k * E = cr b i * (an b k * cr b k) * cr b i * an b k := by
          rw [hEd]; noncomm_ring
      _ = an b k * cr b k * (cr b i * cr b i) * an b k := by rw [hc]; noncomm_ring
      _ = 0 := by rw [cr_sq]; noncomm_ring
  have e3 : F * cr b k = 0 := by
    calc F * cr b k = cr b k * (an b i * cr b k) := by rw [hFd]; noncomm_ring
      _ = 0 := by rw [hki, mul_neg, ← mul_assoc, cr_sq, zero_mul, neg_zero]
  have e4 : F * cr b i - cr b i * F = cr b k := by
    calc F * cr b i - cr b i * F
        = cr b k * (an b i * cr b i) - cr b i * cr b k * an b i := by
          rw [hFd]; noncomm_ring
      _ = cr b k * (an b i * cr b i + cr b i * an b i) := by
          rw [cr_cr b i k]; noncomm_ring
      _ = cr b k := by rw [an_cr_self, mul_one]
  have e5 : F * cr b i * F = 0 := by
    have hc := commute_mul_of_anticomm₂ (cr_an b hik.symm) (cr_cr b k i)
    calc F * cr b i * F = cr b k * (an b i * cr b i) * cr b k * an b i := by
          rw [hFd]; noncomm_ring
      _ = an b i * cr b i * (cr b k * cr b k) * an b i := by rw [hc]; noncomm_ring
      _ = 0 := by rw [cr_sq]; noncomm_ring
  have e6 : E * cr b i = 0 := by
    calc E * cr b i = cr b i * (an b k * cr b i) := by rw [hEd]; noncomm_ring
      _ = 0 := by rw [hik', mul_neg, ← mul_assoc, cr_sq, zero_mul, neg_zero]
  have e8 : cr b k * F = 0 := by rw [hFd, ← mul_assoc, cr_sq, zero_mul]
  have e9 : cr b i * E = 0 := by rw [hEd, ← mul_assoc, cr_sq, zero_mul]
  have s1 : (1 + E) * cr b k = (cr b k + cr b i) * (1 + E) := by
    rw [one_add_mul_eq hE, e1, e2, sub_zero]
  have s2 : (1 - F) * (cr b k + cr b i) = cr b i * (1 - F) := by
    rw [one_sub_mul_eq hF]
    have hFY : F * (cr b k + cr b i) - (cr b k + cr b i) * F = cr b k := by
      rw [mul_add, add_mul, e3, e8, zero_add, zero_add]
      exact e4
    have hFYF : F * (cr b k + cr b i) * F = 0 := by
      rw [mul_add, add_mul, e3, zero_mul, zero_add, e5]
    rw [hFY, hFYF, sub_zero, add_sub_cancel_left]
  have s3 : (1 + E) * cr b i = cr b i * (1 + E) := by
    rw [one_add_mul_eq hE, e6, e9, zero_mul, sub_zero, sub_zero, add_zero]
  calc (1 + E) * (1 - F) * (1 + E) * cr b k = (1 + E) * (1 - F) * ((1 + E) * cr b k) := by
        rw [mul_assoc]
    _ = (1 + E) * ((1 - F) * (cr b k + cr b i)) * (1 + E) := by rw [s1]; noncomm_ring
    _ = (1 + E) * cr b i * (1 - F) * (1 + E) := by rw [s2]; noncomm_ring
    _ = cr b i * ((1 + E) * (1 - F) * (1 + E)) := by rw [s3]; noncomm_ring

theorem chainWeyl_mul_an : chainWeyl b i k * an b k = an b i * chainWeyl b i k := by
  show (1 + cr b i * an b k) * (1 - cr b k * an b i) * (1 + cr b i * an b k) * an b k =
    an b i * ((1 + cr b i * an b k) * (1 - cr b k * an b i) * (1 + cr b i * an b k))
  set E := cr b i * an b k with hEd
  set F := cr b k * an b i with hFd
  have hE : E * E = 0 := chain_E_sq hik
  have hF : F * F = 0 := chain_F_sq hik
  have g1 : E * an b k = 0 := by rw [hEd, mul_assoc, an_sq, mul_zero]
  have g2 : an b k * E = 0 := by
    calc an b k * E = an b k * cr b i * an b k := by rw [hEd]; noncomm_ring
      _ = 0 := by
          rw [an_cr b hik, neg_mul, mul_assoc, an_sq, mul_zero, neg_zero]
  have g3 : F * an b k - an b k * F = -an b i := by
    calc F * an b k - an b k * F
        = cr b k * (an b i * an b k) - an b k * cr b k * an b i := by
          rw [hFd]; noncomm_ring
      _ = -((cr b k * an b k + an b k * cr b k) * an b i) := by
          rw [an_an b i k]; noncomm_ring
      _ = -an b i := by rw [cr_an_self, one_mul]
  have g4 : F * an b k * F = 0 := by
    have hc := commute_mul_of_anticomm₂ (an_an b i k) (an_cr b hik.symm)
    calc F * an b k * F = cr b k * (an b i * (an b k * cr b k)) * an b i := by
          rw [hFd]; noncomm_ring
      _ = cr b k * (an b k * cr b k) * (an b i * an b i) := by rw [hc]; noncomm_ring
      _ = 0 := by rw [an_sq]; noncomm_ring
  have g5 : E * an b i - an b i * E = -an b k := by
    calc E * an b i - an b i * E
        = cr b i * (an b k * an b i) - an b i * cr b i * an b k := by
          rw [hEd]; noncomm_ring
      _ = -((cr b i * an b i + an b i * cr b i) * an b k) := by
          rw [an_an b k i]; noncomm_ring
      _ = -an b k := by rw [cr_an_self, one_mul]
  have g6 : E * an b i * E = 0 := by
    have hc := commute_mul_of_anticomm₂ (an_an b k i) (an_cr b hik)
    calc E * an b i * E = cr b i * (an b k * (an b i * cr b i)) * an b k := by
          rw [hEd]; noncomm_ring
      _ = cr b i * (an b i * cr b i) * (an b k * an b k) := by rw [hc]; noncomm_ring
      _ = 0 := by rw [an_sq]; noncomm_ring
  have s1 : (1 + E) * an b k = an b k * (1 + E) := by
    rw [one_add_mul_eq hE, g1, g2, sub_zero, zero_mul, sub_zero, add_zero]
  have s2 : (1 - F) * an b k = (an b k + an b i) * (1 - F) := by
    rw [one_sub_mul_eq hF, g3, g4, sub_zero, sub_neg_eq_add]
  have s3 : (1 + E) * (an b k + an b i) = an b i * (1 + E) := by
    rw [one_add_mul_eq hE]
    have hEY : E * (an b k + an b i) - (an b k + an b i) * E = -an b k := by
      rw [mul_add, add_mul, g1, g2, zero_add, zero_add]
      exact g5
    have hEYE : E * (an b k + an b i) * E = 0 := by
      rw [mul_add, add_mul, g1, zero_mul, zero_add, g6]
    rw [hEY, hEYE, sub_zero, ← sub_eq_add_neg, add_sub_cancel_left]
  calc (1 + E) * (1 - F) * (1 + E) * an b k = (1 + E) * (1 - F) * ((1 + E) * an b k) := by
        rw [mul_assoc]
    _ = (1 + E) * ((1 - F) * an b k) * (1 + E) := by rw [s1]; noncomm_ring
    _ = (1 + E) * (an b k + an b i) * (1 - F) * (1 + E) := by rw [s2]; noncomm_ring
    _ = an b i * ((1 + E) * (1 - F) * (1 + E)) := by rw [s3]; noncomm_ring

theorem pairWeyl_mul_an : pairWeyl b i k * an b i = -cr b k * pairWeyl b i k := by
  show (1 + cr b i * cr b k) * (1 - an b k * an b i) * (1 + cr b i * cr b k) * an b i =
    -cr b k * ((1 + cr b i * cr b k) * (1 - an b k * an b i) * (1 + cr b i * cr b k))
  set E := cr b i * cr b k with hEd
  set F := an b k * an b i with hFd
  have hE : E * E = 0 := pair_E_sq
  have hF : F * F = 0 := pair_F_sq
  have hka : cr b k * an b i = -(an b i * cr b k) := cr_an b hik.symm
  have kik : cr b k * cr b i * cr b k = 0 := by
    rw [cr_cr b k i, neg_mul, mul_assoc, cr_sq, mul_zero, neg_zero]
  have aka : an b i * an b k * an b i = 0 := by
    rw [an_an b i k, neg_mul, mul_assoc, an_sq, mul_zero, neg_zero]
  have e1 : E * an b i - an b i * E = -cr b k := by
    calc E * an b i - an b i * E = cr b i * (cr b k * an b i) - an b i * cr b i * cr b k := by
          rw [hEd]; noncomm_ring
      _ = -((cr b i * an b i + an b i * cr b i) * cr b k) := by rw [hka]; noncomm_ring
      _ = -cr b k := by rw [cr_an_self, one_mul]
  have e2 : E * an b i * E = 0 := by
    calc E * an b i * E = cr b i * (cr b k * an b i) * cr b i * cr b k := by
          rw [hEd]; noncomm_ring
      _ = -(cr b i * an b i * (cr b k * cr b i * cr b k)) := by rw [hka]; noncomm_ring
      _ = 0 := by rw [kik, mul_zero, neg_zero]
  have s1 : (1 + E) * an b i = (an b i - cr b k) * (1 + E) := by
    rw [one_add_mul_eq hE, e1, e2, sub_zero, ← sub_eq_add_neg]
  have f1 : F * an b i = 0 := by rw [hFd, mul_assoc, an_sq, mul_zero]
  have f2 : an b i * F = 0 := by rw [hFd, ← mul_assoc, aka]
  have f3 : F * cr b k - cr b k * F = -an b i := by
    calc F * cr b k - cr b k * F = an b k * (an b i * cr b k) - cr b k * an b k * an b i := by
          rw [hFd]; noncomm_ring
      _ = -((an b k * cr b k + cr b k * an b k) * an b i) := by
          rw [show an b i * cr b k = -(cr b k * an b i) by rw [hka, neg_neg]]; noncomm_ring
      _ = -an b i := by rw [an_cr_self, one_mul]
  have f4 : F * cr b k * F = 0 := by
    calc F * cr b k * F = an b k * (an b i * cr b k) * an b k * an b i := by
          rw [hFd]; noncomm_ring
      _ = -(an b k * cr b k * (an b i * an b k * an b i)) := by
          rw [show an b i * cr b k = -(cr b k * an b i) by rw [hka, neg_neg]]; noncomm_ring
      _ = 0 := by rw [aka, mul_zero, neg_zero]
  have s2 : (1 - F) * (an b i - cr b k) = -cr b k * (1 - F) := by
    rw [one_sub_mul_eq hF]
    congr 1
    have e3 : F * (an b i - cr b k) - (an b i - cr b k) * F =
        (F * an b i - an b i * F) - (F * cr b k - cr b k * F) := by noncomm_ring
    have e4 : F * (an b i - cr b k) * F = F * an b i * F - F * cr b k * F := by noncomm_ring
    rw [e3, e4, f1, f2, f3, f4, zero_mul]
    abel
  have g1 : E * cr b k = 0 := by rw [hEd, mul_assoc, cr_sq, mul_zero]
  have g2 : cr b k * E = 0 := by rw [hEd, ← mul_assoc, kik]
  have s3 : (1 + E) * (-cr b k) = -cr b k * (1 + E) := by
    have e5 : E * (-cr b k) - (-cr b k) * E = 0 := by rw [mul_neg, neg_mul, g1, g2]; simp
    have e6 : E * (-cr b k) * E = 0 := by rw [mul_neg, g1]; simp
    rw [one_add_mul_eq hE, e5, e6, add_zero, sub_zero]
  calc (1 + E) * (1 - F) * (1 + E) * an b i = (1 + E) * (1 - F) * ((1 + E) * an b i) := by
        rw [mul_assoc]
    _ = (1 + E) * ((1 - F) * (an b i - cr b k)) * (1 + E) := by rw [s1]; noncomm_ring
    _ = (1 + E) * (-cr b k) * (1 - F) * (1 + E) := by rw [s2]; noncomm_ring
    _ = -cr b k * ((1 + E) * (1 - F) * (1 + E)) := by rw [s3]; noncomm_ring

theorem pairWeyl_mul_cr : pairWeyl b i k * cr b i = -an b k * pairWeyl b i k := by
  show (1 + cr b i * cr b k) * (1 - an b k * an b i) * (1 + cr b i * cr b k) * cr b i =
    -an b k * ((1 + cr b i * cr b k) * (1 - an b k * an b i) * (1 + cr b i * cr b k))
  set E := cr b i * cr b k with hEd
  set F := an b k * an b i with hFd
  have hE : E * E = 0 := pair_E_sq
  have hF : F * F = 0 := pair_F_sq
  have hia : cr b i * an b k = -(an b k * cr b i) := cr_an b hik
  have kik : cr b k * cr b i * cr b k = 0 := by
    rw [cr_cr b k i, neg_mul, mul_assoc, cr_sq, mul_zero, neg_zero]
  have aka : an b i * an b k * an b i = 0 := by
    rw [an_an b i k, neg_mul, mul_assoc, an_sq, mul_zero, neg_zero]
  have g1 : E * cr b i = 0 := by
    rw [hEd, mul_assoc, cr_cr b k i, mul_neg, ← mul_assoc, cr_sq, zero_mul, neg_zero]
  have g2 : cr b i * E = 0 := by rw [hEd, ← mul_assoc, cr_sq, zero_mul]
  have s1 : (1 + E) * cr b i = cr b i * (1 + E) := by
    rw [one_add_mul_eq hE, g1, g2, zero_mul, sub_zero, sub_zero, add_zero]
  have f1 : F * cr b i - cr b i * F = an b k := by
    calc F * cr b i - cr b i * F = an b k * (an b i * cr b i) - cr b i * an b k * an b i := by
          rw [hFd]; noncomm_ring
      _ = an b k * (an b i * cr b i + cr b i * an b i) := by rw [hia]; noncomm_ring
      _ = an b k := by rw [an_cr_self, mul_one]
  have f2 : F * cr b i * F = 0 := by
    have e : an b i * cr b i = 1 - cr b i * an b i := by
      rw [← an_cr_self b i, add_sub_cancel_right]
    calc F * cr b i * F = an b k * (an b i * cr b i) * an b k * an b i := by
          rw [hFd]; noncomm_ring
      _ = an b k * an b k * an b i - an b k * cr b i * (an b i * an b k * an b i) := by
          rw [e]; noncomm_ring
      _ = 0 := by rw [an_sq, aka]; simp
  have s2 : (1 - F) * cr b i = (cr b i - an b k) * (1 - F) := by
    rw [one_sub_mul_eq hF, f1, f2, sub_zero]
  have h1 : E * an b k - an b k * E = cr b i := by
    calc E * an b k - an b k * E = cr b i * cr b k * an b k - an b k * cr b i * cr b k := by
          rw [hEd]; noncomm_ring
      _ = cr b i * (cr b k * an b k + an b k * cr b k) := by
          rw [show an b k * cr b i = -(cr b i * an b k) by rw [hia, neg_neg]]; noncomm_ring
      _ = cr b i := by rw [cr_an_self, mul_one]
  have h2 : E * an b k * E = 0 := by
    have e : cr b k * an b k = 1 - an b k * cr b k := by
      rw [← cr_an_self b k, add_sub_cancel_right]
    calc E * an b k * E = cr b i * (cr b k * an b k) * cr b i * cr b k := by
          rw [hEd]; noncomm_ring
      _ = cr b i * cr b i * cr b k - cr b i * an b k * (cr b k * cr b i * cr b k) := by
          rw [e]; noncomm_ring
      _ = 0 := by rw [cr_sq, kik]; simp
  have s3 : (1 + E) * (cr b i - an b k) = -an b k * (1 + E) := by
    rw [one_add_mul_eq hE]
    congr 1
    have e3 : E * (cr b i - an b k) - (cr b i - an b k) * E =
        (E * cr b i - cr b i * E) - (E * an b k - an b k * E) := by noncomm_ring
    have e4 : E * (cr b i - an b k) * E = E * cr b i * E - E * an b k * E := by noncomm_ring
    rw [e3, e4, g1, g2, h1, h2, zero_mul]
    abel
  calc (1 + E) * (1 - F) * (1 + E) * cr b i = (1 + E) * (1 - F) * ((1 + E) * cr b i) := by
        rw [mul_assoc]
    _ = (1 + E) * ((1 - F) * cr b i) * (1 + E) := by rw [s1]; noncomm_ring
    _ = (1 + E) * (cr b i - an b k) * (1 - F) * (1 + E) := by rw [s2]; noncomm_ring
    _ = -an b k * ((1 + E) * (1 - F) * (1 + E)) := by rw [s3]; noncomm_ring

theorem signWeyl_mul_an : signWeyl b i k * an b i = -cr b i * signWeyl b i k := by
  calc signWeyl b i k * an b i = chainWeyl b i k * (pairWeyl b i k * an b i) := by
        rw [signWeyl, mul_assoc]
    _ = -(chainWeyl b i k * cr b k) * pairWeyl b i k := by
        rw [pairWeyl_mul_an hik]; noncomm_ring
    _ = -cr b i * signWeyl b i k := by
        rw [chainWeyl_mul_cr hik, signWeyl]; noncomm_ring

theorem signWeyl_mul_cr : signWeyl b i k * cr b i = -an b i * signWeyl b i k := by
  calc signWeyl b i k * cr b i = chainWeyl b i k * (pairWeyl b i k * cr b i) := by
        rw [signWeyl, mul_assoc]
    _ = -(chainWeyl b i k * an b k) * pairWeyl b i k := by
        rw [pairWeyl_mul_cr hik]; noncomm_ring
    _ = -an b i * signWeyl b i k := by
        rw [chainWeyl_mul_an hik, signWeyl]; noncomm_ring

omit hik in
theorem commute_weyls {g : CliffordAlgebra Q} (h1 : g * cr b i = -(cr b i * g))
    (h2 : g * an b i = -(an b i * g)) (h3 : g * cr b k = -(cr b k * g))
    (h4 : g * an b k = -(an b k * g)) :
    Commute g (chainWeyl b i k) ∧ Commute g (pairWeyl b i k) ∧ Commute g (signWeyl b i k) := by
  have hc := commute_weyl_of (commute_mul_of_anticomm₂ h1 h4) (commute_mul_of_anticomm₂ h3 h2)
  have hp := commute_weyl_of (commute_mul_of_anticomm₂ h1 h3) (commute_mul_of_anticomm₂ h4 h2)
  exact ⟨hc, hp, hc.mul_right hp⟩

end Cliff

namespace CarrierD

open TauCeti TauCeti.TypeDSpinCarrier Cliff RootData

variable {n : ℕ} (hn : 4 ≤ n)

section Matrices

omit hn in
theorem intMap_one' (K : Type*) [Field K] :
    intMap K (1 : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) = 1 := by
  ext a b
  simp [intMap, Matrix.one_apply]

omit hn in
theorem intMap_add' (K : Type*) [Field K]
    (Z W : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) :
    intMap K (Z + W) = intMap K Z + intMap K W := by
  ext a b
  simp [intMap]

omit hn in
theorem isIntOp_one : IsIntOp n 1 1 := by
  unfold IsIntOp
  rw [map_one]
  exact HasIntMatrix.one

omit hn in
theorem IsIntOp.add' {c d : Cl n} {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (h : IsIntOp n c X) (h' : IsIntOp n d Y) : IsIntOp n (c + d) (X + Y) := by
  unfold IsIntOp at *
  rw [map_add]
  exact HasIntMatrix.add h h'

noncomputable def wlMat (i : Fin n) : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
  (1 + rootIntMatrix n hn (.inl i)) * (1 - rootIntMatrix n hn (.inr i)) *
    (1 + rootIntMatrix n hn (.inl i))

noncomputable def wlInv (i : Fin n) : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
  (1 - rootIntMatrix n hn (.inl i)) * (1 + rootIntMatrix n hn (.inr i)) *
    (1 - rootIntMatrix n hn (.inl i))

theorem wlInv_mul (i : Fin n) : wlInv hn i * wlMat hn i = 1 :=
  weyl_inv_mul ((intRootData n hn).sqZero i).ee ((intRootData n hn).sqZero i).ff

variable {hn}

theorem isIntOp_weyl {i : Fin n} {e f : Cl n} (he : IsIntOp n e (rootIntMatrix n hn (.inl i)))
    (hf : IsIntOp n f (rootIntMatrix n hn (.inr i))) :
    IsIntOp n ((1 + e) * (1 - f) * (1 + e)) (wlMat hn i) ∧
      IsIntOp n ((1 - e) * (1 + f) * (1 - e)) (wlInv hn i) :=
  ⟨((isIntOp_one.add' he).mul (isIntOp_one.sub hf)).mul (isIntOp_one.add' he),
    ((isIntOp_one.sub he).mul (isIntOp_one.add' hf)).mul (isIntOp_one.sub he)⟩

omit hn in
theorem conj_transfer {K : Type*} [Field K] {w w' c c' : Cl n}
    {W W' M : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ} (hw : IsIntOp n w W)
    (hw' : IsIntOp n w' W') (hc : IsIntOp n c M) (hww' : w * w' = 1) (hW'W : W' * W = 1)
    (hwc : w * c = c' * w) :
    IsIntOp n c' (W * M * W') ∧ intMap K W * intMap K M = intMap K (W * M * W') * intMap K W := by
  refine ⟨((hw.mul hc).mul hw').congr (by rw [hwc, mul_assoc, hww', mul_one]), ?_⟩
  rw [← intMap_mul, ← intMap_mul, mul_assoc (W * M), hW'W, mul_one]

end Matrices

section Group

variable {hn} {K : Type} [Field K]

noncomputable abbrev nu (i : Fin n) : (rootData n hn K).G :=
  (rootData n hn K).x i 1 * (rootData n hn K).y i (-1) * (rootData n hn K).x i 1

theorem mat_nu (i : Fin n) : (rootData n hn K).mat (nu i) = intMap K (wlMat hn i) := by
  rw [nu, mat_mul, mat_mul, mat_x', mat_y', one_smul, neg_one_smul, wlMat, intMap_mul,
    intMap_mul, intMap_add', intMap_sub', intMap_one', sub_eq_add_neg]
  rfl

variable {D : Subgroup (rootData n hn K).G} {L : Subfield K}

theorem rootOpIn_conj {i : Fin n} {e f c c' : Cl n}
    {M : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (he : IsIntOp n e (rootIntMatrix n hn (.inl i)))
    (hf : IsIntOp n f (rootIntMatrix n hn (.inr i))) (hee : e * e = 0) (hff : f * f = 0)
    (hc : IsIntOp n c M)
    (hwc : (1 + e) * (1 - f) * (1 + e) * c = c' * ((1 + e) * (1 - f) * (1 + e)))
    (hD : ∀ g ∈ D, nu i * g * (nu i)⁻¹ ∈ D) (h : (rootData n hn K).RootOpIn D L (intMap K M)) :
    IsIntOp n c' (wlMat hn i * M * wlInv hn i) ∧
      (rootData n hn K).RootOpIn D L (intMap K (wlMat hn i * M * wlInv hn i)) := by
  obtain ⟨hw, hw'⟩ := isIntOp_weyl he hf
  obtain ⟨h1, h2⟩ := conj_transfer (K := K) hw hw' hc (weyl_mul_inv hee hff) (wlInv_mul hn i) hwc
  exact ⟨h1, h.conj (nu i) hD (by rw [mat_nu]; exact h2)⟩

theorem rootOpIn_conj₂ {i j : Fin n} {e f e' f' c c' c'' : Cl n}
    {M : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (he : IsIntOp n e (rootIntMatrix n hn (.inl i)))
    (hf : IsIntOp n f (rootIntMatrix n hn (.inr i))) (hee : e * e = 0) (hff : f * f = 0)
    (he' : IsIntOp n e' (rootIntMatrix n hn (.inl j)))
    (hf' : IsIntOp n f' (rootIntMatrix n hn (.inr j))) (hee' : e' * e' = 0) (hff' : f' * f' = 0)
    (hc : IsIntOp n c M)
    (hwc : (1 + e') * (1 - f') * (1 + e') * c = c' * ((1 + e') * (1 - f') * (1 + e')))
    (hwc' : (1 + e) * (1 - f) * (1 + e) * c' = c'' * ((1 + e) * (1 - f) * (1 + e)))
    (hD : ∀ g ∈ D, nu i * nu j * g * (nu i * nu j)⁻¹ ∈ D)
    (h : (rootData n hn K).RootOpIn D L (intMap K M)) :
    IsIntOp n c'' (wlMat hn i * (wlMat hn j * M * wlInv hn j) * wlInv hn i) ∧
      (rootData n hn K).RootOpIn D L
        (intMap K (wlMat hn i * (wlMat hn j * M * wlInv hn j) * wlInv hn i)) := by
  obtain ⟨hw, hw'⟩ := isIntOp_weyl he hf
  obtain ⟨hv, hv'⟩ := isIntOp_weyl he' hf'
  obtain ⟨h1, h2⟩ := conj_transfer (K := K) hv hv' hc (weyl_mul_inv hee' hff') (wlInv_mul hn j)
    hwc
  obtain ⟨h3, h4⟩ := conj_transfer (K := K) hw hw' h1 (weyl_mul_inv hee hff) (wlInv_mul hn i)
    hwc'
  refine ⟨h3, h.conj (nu i * nu j) hD ?_⟩
  rw [mat_mul, mat_nu, mat_nu]
  calc intMap K (wlMat hn i) * intMap K (wlMat hn j) * intMap K M
      = intMap K (wlMat hn i) * (intMap K (wlMat hn j) * intMap K M) := mul_assoc _ _ _
    _ = intMap K (wlMat hn i) * intMap K (wlMat hn j * M * wlInv hn j) *
        intMap K (wlMat hn j) := by rw [h2]; exact (mul_assoc _ _ _).symm
    _ = _ := by rw [h4]; exact mul_assoc _ _ _

end Group

end CarrierD

end CFSG.RankThree.PartTwo.Census.Spin
